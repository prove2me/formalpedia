-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Prod
-- name    : ProEtale_Mathlib_RingTheory_Etale_Prod
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:06.157798+00:00
-- url     : https://prove2.me/theorems/b7543191-b275-50cb-9037-7c7242e1759d
-- title:
--   Binary products of étale, formally étale, formally smooth or formally unramified algebras
-- statement:
--   Let $R$ be a commutative ring and $A$, $B$ commutative $R$-algebras. The file shows that the product algebra $A \times B$ inherits the following properties when both $A$ and $B$ have them:
--
--   1. formally unramified;
--   2. formally smooth;
--   3. formally étale;
--   4. finitely presented;
--   5. étale.
--
--   Each case follows from the corresponding result for finite products $\prod_{i \in \mathrm{Fin}\,2}$, transported along the isomorphism $\prod_{i\in\{0,1\}} A_i \cong A_0 \times A_1$.
--
--   These instances let étale-local constructions use decompositions $A \times B$, for instance splitting off idempotents.
--
--   **Formalization Note** The instances are `Algebra.FormallyUnramified.prod`, `Algebra.FormallySmooth.prod`, `Algebra.FormallyEtale.prod`, `Algebra.FinitePresentation.prod` and `Algebra.Etale.prod`. $R$, $A$ and $B$ must live in the same universe `u`. A private family `fin2Fam A B : Fin 2 → Type u`, defined by pattern matching, is used instead of `![A, B]` so that its components reduce definitionally.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Etale/Prod.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.RingHom.FinitePresentation
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Formal-étaleness of binary products of rings

We deduce that the binary product of two formally-étale `R`-algebras is formally-étale,
and likewise for étale, formally unramified, and formally smooth, by transferring the
finite-Pi case from `Mathlib.RingTheory.Etale.Pi`.

Rather than using `Matrix.vecCons` (whose elaboration does not eagerly reduce
`![A, B] 0` to `A`), we use an explicit case-based family `fin2Fam A B i`
defined by `Fin` pattern matching on `Fin 2`, so that `fin2Fam A B 0 = A` and
`fin2Fam A B 1 = B` reduce definitionally.

## Main results

- `Algebra.FormallyEtale.prod`: `A × B` is `R`-formally-étale when `A` and `B` are.
- `Algebra.Etale.prod`: `A × B` is `R`-étale when `A` and `B` are.
- `Algebra.FormallyUnramified.prod`: `A × B` is `R`-formally-unramified when `A` and `B` are.
- `Algebra.FormallySmooth.prod`: `A × B` is `R`-formally-smooth when `A` and `B` are.
-/

universe u

namespace Algebra

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A binary family `Fin 2 → Type u`. Definitionally `fin2Fam A B 0 = A` and
`fin2Fam A B 1 = B`. -/
private def fin2Fam (A B : Type u) : Fin 2 → Type u
  | ⟨0, _⟩ => A
  | ⟨1, _⟩ => B

private instance fin2Fam_commRing :
    ∀ i : Fin 2, CommRing (fin2Fam A B i)
  | ⟨0, _⟩ => ‹CommRing A›
  | ⟨1, _⟩ => ‹CommRing B›

private instance fin2Fam_algebra :
    ∀ i : Fin 2, Algebra R (fin2Fam A B i)
  | ⟨0, _⟩ => ‹Algebra R A›
  | ⟨1, _⟩ => ‹Algebra R B›

instance FormallyUnramified.prod [FormallyUnramified R A] [FormallyUnramified R B] :
    FormallyUnramified R (A × B) :=
  have : ∀ i : Fin 2, FormallyUnramified R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallyUnramified R A›
    | ⟨1, _⟩ => ‹FormallyUnramified R B›
  FormallyUnramified.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance FormallySmooth.prod [FormallySmooth R A] [FormallySmooth R B] :
    FormallySmooth R (A × B) :=
  have : ∀ i : Fin 2, FormallySmooth R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallySmooth R A›
    | ⟨1, _⟩ => ‹FormallySmooth R B›
  FormallySmooth.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance FormallyEtale.prod [FormallyEtale R A] [FormallyEtale R B] :
    FormallyEtale R (A × B) :=
  have : ∀ i : Fin 2, FormallyEtale R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallyEtale R A›
    | ⟨1, _⟩ => ‹FormallyEtale R B›
  FormallyEtale.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

/-- `A × B` is finitely presented as an `R`-algebra when both factors are. -/
instance FinitePresentation.prod [FinitePresentation R A] [FinitePresentation R B] :
    FinitePresentation R (A × B) :=
  have : ∀ i : Fin 2, FinitePresentation R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FinitePresentation R A›
    | ⟨1, _⟩ => ‹FinitePresentation R B›
  have : FinitePresentation R ((i : Fin 2) → fin2Fam A B i) :=
    Algebra.FinitePresentation.pi (fin2Fam A B)
  Algebra.FinitePresentation.equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance Etale.prod [Etale R A] [Etale R B] : Etale R (A × B) where

end Algebra


