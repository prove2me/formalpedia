-- Prove2me | Definitions.Def_ModularCurve_NodeLocalized
-- name    : ModularCurve_NodeLocalized
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/fd89e081-e1c4-5254-b856-ea89f364038f
-- title:
--   Local ring of the Kronecker plane model at a closed point mod p
-- statement:
--   Fix $N \ge 1$, a commutative ring $L$, a subring $A \subseteq L$, a field $k$, a ring homomorphism $\mathrm{red} \colon A \to k$ and two elements $a, b \in k$. Three objects are defined inside the Laurent series ring $L(\!(q)\!)$ (Hahn series over $\mathbb{Z}$ with coefficients in $L$).
--
--   First, `modularEval` is the ring homomorphism from the polynomial ring $A[X_0, X_1]$ in two variables to $L(\!(q)\!)$ obtained by evaluating: coefficients in $A$ are sent to the corresponding constant Laurent series via `CharPReduction.constSeries`, the first variable to the $j$-expansion $j(q) = q^{-1} + \cdots$ (`jqModC L`), and the second to its $N$-fold substitution $j(q^N)$ (`jqNModC L N`). Thus $p \mapsto p(j, j_N)$. Second, `pointEval` is the homomorphism $A[X_0, X_1] \to k$ evaluating coefficients through $\mathrm{red}$ and the two variables at $a$ and $b$, so $p \mapsto \bar p(a,b)$.
--
--   Third, `modularLocalizedAtPoint` is the subring of $L(\!(q)\!)$ whose elements are those $f$ for which there exist $r, s \in A[X_0, X_1]$ with $\bar s(a,b) \ne 0$ in $k$ and $f \cdot s(j, j_N) = r(j, j_N)$ in $L(\!(q)\!)$; closure under zero, one, addition, negation and multiplication is part of the definition, obtained by the usual clearing of denominators. This realises the localisation of the image $A[j, j_N]$ of the coordinate ring of the Kronecker plane model at the multiplicative set of polynomials not vanishing at the point $(a,b)$ of the fibre over $\mathrm{red}$, as a subring of the ambient series ring rather than as an abstract localisation.
--
--   The accompanying lemmas record the membership criterion by definition, and that every value $p(j, j_N)$ of a polynomial lies in this subring (take $s = 1$).
--
--   **Relation to Mathlib.** Mathlib's localisation machinery (`Localization`, `IsLocalization`) builds a new ring; here the localisation is instead carved out as a `Subring` of the ambient Laurent series ring, so that its elements are honest $q$-expansions. The modular inputs `jqModC`, `jqNModC` and the ambient reduction formalism are the project's own.
--
--   **Where it is used.** These local rings belong to the project's treatment of modular functions modulo a prime: the plane model of $X_0(N)$ cut out by the modular equation in the $(j, j_N)$-coordinates is localised at a closed point $(a,b)$ of its reduction, the case $N = q$, $b = a^q$ in characteristic $q$ being the situation of the two Kronecker branches crossing above a supersingular $j$-invariant. This analysis of $X_0(q)$ in characteristic $q$ underlies the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_NodeLocalized.lean

import Mathlib
import Definitions.Def_ModularCurve_CharPReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def modularEval : MvPolynomial (Fin 2) A →+* LaurentSeries L :=
  MvPolynomial.eval₂Hom (CharPReduction.constSeries A) ![jqModC L, jqNModC L N]

def pointEval : MvPolynomial (Fin 2) A →+* k :=
  MvPolynomial.eval₂Hom red ![a, b]

def modularLocalizedAtPoint : Subring (LaurentSeries L) where
  carrier := {f | ∃ r s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ f * modularEval N A s = modularEval N A r}
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, map_zero, zero_mul]⟩
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * t + u * s, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (modularEval N A s * modularEval N A t)
        = f * modularEval N A s * modularEval N A t + g * modularEval N A t * modularEval N A s := by ring
      _ = modularEval N A r * modularEval N A t + modularEval N A u * modularEval N A s := by rw [hf, hg]
  neg_mem' := by
    rintro f ⟨r, s, hs, hf⟩
    exact ⟨-r, s, hs, by rw [neg_mul, hf, map_neg]⟩
  mul_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * u, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_mul]
    calc f * g * (modularEval N A s * modularEval N A t)
        = (f * modularEval N A s) * (g * modularEval N A t) := by ring
      _ = modularEval N A r * modularEval N A u := by rw [hf, hg]

theorem mem_modularLocalizedAtPoint {f : LaurentSeries L} :
    f ∈ modularLocalizedAtPoint N A red a b ↔
      ∃ r s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ f * modularEval N A s = modularEval N A r :=
  Iff.rfl

theorem modularEval_mem_modularLocalizedAtPoint (p : MvPolynomial (Fin 2) A) :
    modularEval N A p ∈ modularLocalizedAtPoint N A red a b :=
  ⟨p, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩

end Point

end NodeLocalized
end ModularCurve

end


