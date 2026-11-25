-- Prove2me | Definitions.Def_FiniteFields_Etale_FiniteCoefficients
-- name    : FiniteFields_Etale_FiniteCoefficients
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:28:13.071803+00:00
-- url     : https://prove2.me/theorems/b6407430-4738-4dc8-8bd9-b30214304d34
-- title:
--   Finite $\ell$-adic coefficient groups $\mathbb Z/\ell^{n+1}\mathbb Z$ and their reductions
-- statement:
--   For a prime $\ell$ and $n\ge 0$, the finite coefficient group of level $n$ is the abelian group $\mathbb Z/\ell^{n+1}\mathbb Z$. For $m\le n$, the reduction map from level $n$ to level $m$ is the canonical surjection $\mathbb Z/\ell^{n+1}\mathbb Z\to\mathbb Z/\ell^{m+1}\mathbb Z$. These groups and maps form the projective system $(\mathbb Z/\ell^{n+1})_n$ whose limit is $\mathbb Z_\ell$.
-- source:
--   P. Deligne, Cohomologie étale (SGA 4½), « Rapport sur la formule des traces »; E. Freitag, R. Kiehl, Étale Cohomology and the Weil Conjecture, Chapter I (ℓ-adic sheaves).

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry

universe u

-- Portage v4.33 : option nécessaire avec Mathlib `0df444a` (comme dans `Sites/Etale.lean`).
set_option backward.isDefEq.respectTransparency.types false

/-- The level-`n` finite ell-adic coefficient group `Z / ell^(n+1) Z`.

The prime hypothesis ensures that every displayed coefficient group is genuinely finite. -/
abbrev finiteEllAdicCoefficientGroup (ell n : ℕ) [Fact ell.Prime] : Ab :=
  AddCommGrpCat.of (ZMod (ell ^ (n + 1)))

/-- Canonical reduction from level `n` to level `m` when `m <= n`. -/
def finiteEllAdicReduction (ell : ℕ) [Fact ell.Prime] {m n : ℕ} (h : m ≤ n) :
    finiteEllAdicCoefficientGroup ell n ⟶ finiteEllAdicCoefficientGroup ell m :=
  AddCommGrpCat.ofHom <|
    (ZMod.castHom (pow_dvd_pow ell (Nat.add_le_add_right h 1))
      (ZMod (ell ^ (m + 1)))).toAddMonoidHom





















end FiniteFields.Etale


