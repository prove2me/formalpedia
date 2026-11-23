-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_AGBridge
-- name    : NOFSeparation750_CodedGIP_AGBridge
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:52:50.663231+00:00
-- url     : https://prove2.me/theorems/528cebd6-be9e-4c7d-a7f2-a00b138886ed
-- title:
--   One-point Riemann–Roch evaluation-code interface
-- statement:
--   For a finite field $\mathbb F$, a function field $K/\mathbb F$, a global place $P_\infty$, and $A\in\mathbb N$, this module defines the one-point divisor $A P_\infty$. For a linear evaluation map $E:K\to\mathbb F^r$ it also defines the evaluation code $E(L(G))$ of a Riemann–Roch space $L(G)$.
--
--   The structural API records evaluation of a one-point divisor, monotonicity in its pole bound, and the fact that an effective divisor gives a nonzero evaluation code when $E(1)=1$ and $r>0$. The last assertion uses only regularity supplied by membership in $L(G)$; it does not assert that constants are regular at arbitrary places unrelated to $G$.
-- source:
--   Wang–Wang–Wu, STOC 2027 submission #750, Appendix A.1 pp.11 and A.3 pp.12–13: one-point Riemann–Roch spaces, their evaluations, and the code nonzeroness needed for compatibility.

import Definitions.Def_NOFSeparation750_CodedGIP_Codes
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
noncomputable section

namespace NOFSeparation750.CodedGIP.AGBridge

variable {F : Type} [Field F] [Finite F] {K : Type*} [Field K] [Algebra F K]

/-- The divisor $A P$, supported only at the global place $P$. -/
def poleDivisor (P : GlobalPlace F K) (A : ℕ) : Divisor (GlobalPlace F K) :=
  A • Finsupp.single P 1

/-- The image of a Riemann--Roch space under an arbitrary linear evaluation map. -/
def rrEvaluationCode {r : ℕ} (E : K →ₗ[F] (Fin r → F))
    (G : Divisor (GlobalPlace F K)) : NOFSeparation750.CodedGIP.LinearCode F r :=
  LinearMap.range (E.comp (GlobalPlace.riemannRochSubmodule G).subtype)

@[simp] lemma poleDivisor_apply_self (P : GlobalPlace F K) (A : ℕ) :
    poleDivisor P A P = A := by
  simp [poleDivisor]

@[simp] lemma poleDivisor_apply_of_ne {P Q : GlobalPlace F K} (A : ℕ) (h : Q ≠ P) :
    poleDivisor P A Q = 0 := by
  simp [poleDivisor, h]

@[simp] lemma nsmul_poleDivisor (P : GlobalPlace F K) (k A : ℕ) :
    k • poleDivisor P A = poleDivisor P (k * A) := by
  ext Q
  by_cases h : Q = P
  · subst Q
    simp [poleDivisor]
  · simp [poleDivisor, h]

lemma poleDivisor_mono {P : GlobalPlace F K} {A B : ℕ} (hAB : A ≤ B) :
    poleDivisor P A ≤ poleDivisor P B := by
  intro Q
  by_cases h : Q = P
  · subst Q
    simpa using hAB
  · simp [h]

lemma rrEvaluationCode_mono {r : ℕ} (E : K →ₗ[F] (Fin r → F))
    {G H : Divisor (GlobalPlace F K)} (hGH : G ≤ H) :
    rrEvaluationCode E G ≤ rrEvaluationCode E H := by
  rintro x ⟨f, rfl⟩
  refine ⟨⟨f, ?_⟩, rfl⟩
  intro P
  exact (f.property P).trans (WithZero.exp_le_exp.mpr (hGH P))

lemma one_mem_riemannRochSubmodule_of_nonneg {G : Divisor (GlobalPlace F K)} (hG : 0 ≤ G) :
    (1 : K) ∈ GlobalPlace.riemannRochSubmodule G := by
  intro P
  rw [map_one]
  have h := WithZero.exp_le_exp.mpr (hG P)
  simpa using h

lemma zero_le_poleDivisor (P : GlobalPlace F K) (A : ℕ) : 0 ≤ poleDivisor P A := by
  intro Q
  by_cases h : Q = P
  · subst Q
    simp [poleDivisor]
  · simp [poleDivisor, h]

/-- An evaluation map preserving the constant function gives a nonzero evaluation code
on a nonempty coordinate set whenever the divisor is effective. -/
lemma rrEvaluationCode_ne_bot_of_one {r : ℕ} (E : K →ₗ[F] (Fin r → F)) (hone : E 1 = 1)
    {G : Divisor (GlobalPlace F K)} (hG : 0 ≤ G) (hr : 0 < r) :
    rrEvaluationCode E G ≠ ⊥ := by
  intro hbot
  have hmem : E 1 ∈ rrEvaluationCode E G :=
    ⟨⟨1, one_mem_riemannRochSubmodule_of_nonneg hG⟩, rfl⟩
  rw [hbot, Submodule.mem_bot, hone] at hmem
  have hcoord := congrFun hmem ⟨0, hr⟩
  simpa using hcoord

end NOFSeparation750.CodedGIP.AGBridge


