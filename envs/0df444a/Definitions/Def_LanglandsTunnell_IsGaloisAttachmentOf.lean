-- Prove2me | Definitions.Def_LanglandsTunnell_IsGaloisAttachmentOf
-- name    : LanglandsTunnell_IsGaloisAttachmentOf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/28138531-f989-5a43-8bb7-173e1e802a25
-- title:
--   Attachment of an octahedral datum to a mod 3 representation
-- statement:
--   This module defines a single predicate, `IsGaloisAttachmentOf`, relating a residual representation to the Hecke data carried by an octahedral Galois datum. Its arguments are a group homomorphism $\rho$ from the absolute Galois group of $\mathbb{Q}$, realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_2(\mathbb{Z}/3)$; a datum $D$ of the project's type `OctahedralGaloisDatum ℚ (ℤ√(-2))`, i.e. a finite group $G$ together with a surjection $G \twoheadrightarrow S_4$ (the permutations of `Fin 4`) and a Hecke eigensystem `D.attached` over $\mathbb{Z}[\sqrt{-2}]$ for the field $\mathbb{Q}$ (a record consisting of a nonzero level ideal and two functions $a, b$ on the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$); and a finite set $S$ of natural numbers, the excluded primes.
--
--   The predicate asserts: for every prime $p$ with $p \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ (in the sense that $p$ is a non-unit of $A$), and every $\sigma$ in the Galois group that is a Frobenius at $p$ for $A$ — that is, $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{p}$ — one has
--   $$\mathrm{red}\big(a_{p}\big) \;=\; \mathrm{tr}\,\rho(\sigma) \in \mathbb{Z}/3,$$
--   where $a_{p} =$ `D.attached.a (ratPrime p)` is the $a$-value of the attached eigensystem at the height-one prime of $\mathcal{O}_{\mathbb{Q}}$ corresponding to $p$, $\mathrm{red} : \mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ is the ring homomorphism sending $\sqrt{-2}$ to $-1$ (legitimate since $(-1)^2 = -2$ in $\mathbb{Z}/3$), and the trace is that of the underlying $2 \times 2$ matrix of $\rho(\sigma)$.
--
--   Note that only the traces of Frobenius elements, and only the $a$-values, are constrained: nothing is required of the $b$-values (determinants), of the level, or of the octahedral group-theoretic part of $D$, and no compatibility at primes in $S$ is imposed. Thus the predicate is a mod 3 Frobenius-trace matching condition, not an assertion that $\rho$ is realised by $D$ up to isomorphism.
--
--   **Relation to Mathlib.** Mathlib has no notion of Hecke eigensystem or of octahedral Galois datum; these are the project's own records. The predicates [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51) are likewise defined in the project, on top of Mathlib's decomposition subgroup and residue field of a valuation subring; `red` is obtained from Mathlib's `Zsqrtd.lift`.
--
--   **Where it is used.** The predicate is the interface between the mod 3 representation coming from a Frey curve and the automorphic side in the Langlands–Tunnell step: an octahedral datum whose attached Hecke eigensystem matches the Frobenius traces of $\rho$ modulo $3$ outside a finite set of primes is what allows a cuspidal eigensystem with the same Frobenius data to be produced and then realised by a weight one form, and hence by a weight two form congruent to it modulo $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_IsGaloisAttachmentOf.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_OctahedralDatum
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm FLT.TunnellOctahedralGlobalCarrier FLT.ExplicitLift
open scoped MatrixGroups

namespace FLT.TunnellOctahedralGlobalCarrier

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def IsGaloisAttachmentOf (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (D : OctahedralGaloisDatum ℚ (ℤ√(-2))) (S : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ S →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (D.attached.a (ratPrime p))
          = ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

end FLT.TunnellOctahedralGlobalCarrier


