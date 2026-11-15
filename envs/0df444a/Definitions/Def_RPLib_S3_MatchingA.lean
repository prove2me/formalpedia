-- Prove2me | Definitions.Def_RPLib_S3_MatchingA
-- name    : RPLib_S3_MatchingA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:45.954747+00:00
-- url     : https://prove2.me/theorems/189b774d-a524-4215-9c63-1bd4fc3b2a15
-- title:
--   Weight-two Ramanujan-Petersson library: the operator `Φ` (`TracePhiPow`, `RootOfPhi`)
-- statement:
--   The operator `Φ` (`TracePhiPow`, `RootOfPhi`).
--
--   `Φ = [[T_p, -p^{k-1}⟨p⟩], [1, 0]]` on `S ⊕ S`, `S = S_k(Γ₁(M))`.
--   * `blk A B C D`: the block operator `[[A, B], [C, D]]`; `blk_mul`, `trace_blk` (`= tr A + tr D`).
--   * `phiOp_eq_blk`, `phiOp_pow_two_add`: `Φ^{m+2} = [[T_{p^{m+2}}, -c⟨p⟩T_{p^{m+1}}], [T_{p^{m+1}}, -c⟨p⟩T_{p^m}]]`
--     (`c = p^{k-1}`, uses `T_p ⟨p⟩ = ⟨p⟩ T_p`).
--   * **`tracePhiPow : TracePhiPow`**, **`rootOfPhi : RootOfPhi`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S1_FinDim

/-!
# S3-Matching, part A: the operator `Φ` (`TracePhiPow`, `RootOfPhi`)

`Φ = [[T_p, -p^{k-1}⟨p⟩], [1, 0]]` on `S ⊕ S`, `S = S_k(Γ₁(M))`.
* `blk A B C D`: the block operator `[[A, B], [C, D]]`; `blk_mul`, `trace_blk` (`= tr A + tr D`).
* `phiOp_eq_blk`, `phiOp_pow_two_add`: `Φ^{m+2} = [[T_{p^{m+2}}, -c⟨p⟩T_{p^{m+1}}], [T_{p^{m+1}}, -c⟨p⟩T_{p^m}]]`
  (`c = p^{k-1}`, uses `T_p ⟨p⟩ = ⟨p⟩ T_p`).
* **`tracePhiPow : TracePhiPow`**, **`rootOfPhi : RootOfPhi`**.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

open RamanujanPetersson.Diamond RamanujanPetersson.Hecke

section Blk

variable {S : Type*} [AddCommGroup S] [Module ℂ S]

/-- The block operator `[[A, B], [C, D]]` on `S × S`. -/
def blk (A B C D : Module.End ℂ S) : Module.End ℂ (S × S) :=
  LinearMap.prod (A ∘ₗ LinearMap.fst ℂ S S + B ∘ₗ LinearMap.snd ℂ S S)
    (C ∘ₗ LinearMap.fst ℂ S S + D ∘ₗ LinearMap.snd ℂ S S)

lemma blk_apply (A B C D : Module.End ℂ S) (x : S × S) :
    blk A B C D x = (A x.1 + B x.2, C x.1 + D x.2) := rfl

lemma blk_mul (A B C D A' B' C' D' : Module.End ℂ S) :
    blk A B C D * blk A' B' C' D' =
      blk (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, blk_apply, LinearMap.add_apply, map_add, Prod.mk.injEq]
  constructor <;> abel

lemma blk_eq (A B C D : Module.End ℂ S) :
    blk A B C D = LinearMap.prodMap A D + (LinearMap.inl ℂ S S ∘ₗ B ∘ₗ LinearMap.snd ℂ S S) +
      (LinearMap.inr ℂ S S ∘ₗ C ∘ₗ LinearMap.fst ℂ S S) := by
  refine LinearMap.ext fun x => Prod.ext ?_ ?_ <;> simp [blk_apply, add_comm]

/-- `[[T, -cD], [1, 0]]^{m+2}` for `T cD = cD T` and `A` the recursion `A_{m+2} = T A_{m+1} - cD A_m`. -/
lemma blk_pow_two_add (T cD : Module.End ℂ S) (A : ℕ → Module.End ℂ S) (hTD : T * cD = cD * T)
    (h0 : A 0 = 1) (h1 : A 1 = T) (hrec : ∀ m, A (m + 2) = T * A (m + 1) - cD * A m) (m : ℕ) :
    blk T (-cD) 1 0 ^ (m + 2) = blk (A (m + 2)) (-cD * A (m + 1)) (A (m + 1)) (-cD * A m) := by
  induction m with
  | zero =>
    have eB : T * -cD + -cD * 0 = -cD * T := by rw [mul_neg, hTD, mul_zero, add_zero, neg_mul]
    rw [pow_two, blk_mul, eB, hrec 0, h1, h0]
    congr 1 <;> noncomm_ring
  | succ m ih =>
    have h3 : A (m + 2 + 1) = T * A (m + 2) - cD * A (m + 1) := hrec (m + 1)
    have eB : T * (-cD * A (m + 1)) = -cD * (T * A (m + 1)) := by
      rw [neg_mul, neg_mul, mul_neg, ← mul_assoc, hTD, mul_assoc]
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ', ih, blk_mul, show m + 1 + 1 = m + 2 by omega, h3, eB,
      hrec m]
    congr 1 <;> noncomm_ring

lemma trace_blk [Module.Free ℂ S] [Module.Finite ℂ S] (A B C D : Module.End ℂ S) :
    LinearMap.trace ℂ (S × S) (blk A B C D) = LinearMap.trace ℂ S A + LinearMap.trace ℂ S D := by
  have h1 : LinearMap.trace ℂ (S × S) (LinearMap.inl ℂ S S ∘ₗ B ∘ₗ LinearMap.snd ℂ S S) = 0 := by
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.snd_comp_inl, LinearMap.comp_zero,
      map_zero]
  have h2 : LinearMap.trace ℂ (S × S) (LinearMap.inr ℂ S S ∘ₗ C ∘ₗ LinearMap.fst ℂ S S) = 0 := by
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.fst_comp_inr, LinearMap.comp_zero,
      map_zero]
  rw [blk_eq, map_add, map_add, h1, h2, LinearMap.trace_prodMap', add_zero, add_zero]

end Blk

variable {M : ℕ} [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ)

lemma phiOp_eq_blk :
    phiOp p hpM k = blk (heckeT p k) (-(((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM))) 1 0 := by
  refine LinearMap.ext fun x => Prod.ext ?_ ?_ <;> simp [phiOp, blk_apply, sub_eq_add_neg]

lemma commute_T_cD :
    Commute (heckeT (M := M) p k) (((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM)) :=
  (heckeT_commute_diamond (p := p) k (unitP hpM)).smul_right _

/-- `Φ^{m+2}` in block form. -/
lemma phiOp_pow_two_add (m : ℕ) :
    phiOp p hpM k ^ (m + 2) =
      blk (Tpow p hpM k (m + 2)) (-(((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM)) * Tpow p hpM k (m + 1))
        (Tpow p hpM k (m + 1)) (-(((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM)) * Tpow p hpM k m) := by
  rw [phiOp_eq_blk]
  exact blk_pow_two_add _ _ (Tpow p hpM k) (commute_T_cD p hpM k).eq rfl rfl (fun _ => rfl) m

/-- **(S3-Matching) Power sums of `Φ`.** -/
theorem tracePhiPow : TracePhiPow := by
  intro M _ p _ hpM k
  have := RamanujanPetersson.FinDim.finiteDimensional_cuspForm_Gamma1 M k
  refine ⟨?_, fun m => ?_⟩
  · rw [phiOp_eq_blk, trace_blk, map_zero, add_zero]
  · rw [phiOp_pow_two_add, trace_blk, neg_mul, map_neg, smul_mul_assoc, map_smul, smul_eq_mul]
    ring

/-- **(S3-Matching) Every Hecke root of a `T_p`, `⟨p⟩`-eigenform is an eigenvalue of `Φ`.** -/
theorem rootOfPhi : RootOfPhi := by
  intro M _ p _ hpM k F a c α hF hT hD hα
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := (α • F, F)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, phiOp_eq_blk, blk_apply]
    simp only [map_smul, hT, LinearMap.neg_apply, LinearMap.smul_apply, hD, Module.End.one_apply,
      LinearMap.zero_apply, add_zero, Prod.smul_mk]
    refine Prod.ext ?_ rfl
    simp only [smul_smul, ← neg_smul, ← add_smul]
    congr 1
    linear_combination -hα
  · intro h
    exact hF (congrArg Prod.snd h)

end RamanujanPetersson.S3.Match


