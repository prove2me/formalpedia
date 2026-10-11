-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_freqSeries_principalFreq_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T15:14:19.370175+00:00
-- url     : https://prove2.me/submissions/fb46e070-88bf-4e28-9244-bd1df49091aa

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul

section
/-! # C3A_Sieve: Euler products of multiplicative functions of four ideals

A function `f` on 4-tuples of ideals of `𝓞 F`, supported on exterior tuples, with
`f (P^e · y) = A P e · f y` for exterior primes `P` and exterior `y` prime to `P`, and absolutely
summable, has the Euler product `∑' f = ∏'_P ∑'_e A P e` over the exterior primes (`euler4`).
Proof: the finite sieve `∑' f = (∏_{P ∈ T} L_P) · ∑'_{x prime to T} f x` (induction on `T`) and a
tail estimate. Also a bound `‖f‖ ≤ B` for multiplicative majorants (`norm_le_of_mul`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

/-- 4-tuples of ideals. -/
abbrev Tup (F : Type*) [Field F] [NumberField F] : Type _ :=
  Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F)

/-- Exponent vectors. -/
abbrev Exps : Type := ℕ × ℕ × ℕ × ℕ

/-- `P^e · x`, coordinatewise. -/
def pw (P : Ideal (𝓞 F)) (e : Exps) (x : Tup F) : Tup F :=
  (P ^ e.1 * x.1, P ^ e.2.1 * x.2.1, P ^ e.2.2.1 * x.2.2.1, P ^ e.2.2.2 * x.2.2.2)

/-- The unit tuple. -/
def one4 : Tup F := (⊤, ⊤, ⊤, ⊤)

/-- Exterior tuples. -/
def Om (𝔪 : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | IsExterior 𝔪 x.1 ∧ IsExterior 𝔪 x.2.1 ∧ IsExterior 𝔪 x.2.2.1 ∧ IsExterior 𝔪 x.2.2.2}

/-- Tuples prime to `P`. -/
def CopP (P : Ideal (𝓞 F)) : Set (Tup F) :=
  {x | ¬ x.1 ≤ P ∧ ¬ x.2.1 ≤ P ∧ ¬ x.2.2.1 ≤ P ∧ ¬ x.2.2.2 ≤ P}

/-- Tuples prime to every member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Tup F) := {x | ∀ P ∈ T, x ∈ CopP P}

/-- Exterior primes. -/
def IsEP (𝔪 P : Ideal (𝓞 F)) : Prop := P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤

/-- The type of exterior primes. -/
abbrev EP (𝔪 : Ideal (𝓞 F)) : Type _ := {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤}

lemma two_le_absNorm {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

lemma decomp1 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ∃ k J, I = P ^ k * J ∧ ¬ J ≤ P := by
  intro I
  induction hN : Ideal.absNorm I using Nat.strong_induction_on generalizing I with
  | _ N ih =>
  intro hI
  by_cases hle : I ≤ P
  · obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ : J ≠ ⊥ := by rintro rfl; exact hI (by simp)
    have hlt : Ideal.absNorm J < N := by
      rw [← hN, map_mul]
      have := two_le_absNorm hP hP0
      have hJ0 : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      have := Nat.pos_of_ne_zero hJ0
      nlinarith
    obtain ⟨k, K, hK, hKP⟩ := ih _ hlt J rfl hJ
    exact ⟨k + 1, K, by rw [hK, pow_succ', mul_assoc], hKP⟩
  · exact ⟨0, I, by simp, hle⟩

lemma cancel1 {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {a b : ℕ} {J J' : Ideal (𝓞 F)}
    (hJ : ¬ J ≤ P) (hJ' : ¬ J' ≤ P) (h : P ^ a * J = P ^ b * J') : a = b ∧ J = J' := by
  have hP : (P : Ideal (𝓞 F)) ≠ 0 := hP0
  have key : ∀ {a b : ℕ} {J J' : Ideal (𝓞 F)}, ¬ J ≤ P → a ≤ b → P ^ a * J = P ^ b * J' →
      a = b ∧ J = J' := by
    intro a b J J' hJ hab h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero a hP) h
    rcases c with _ | c
    · simp only [pow_zero, one_mul] at h2
      exact ⟨rfl, h2⟩
    · exfalso; apply hJ; rw [h2, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  rcases le_total a b with hab | hab
  · exact key hJ hab h
  · obtain ⟨h1, h2⟩ := key hJ' hab h.symm
    exact ⟨h1.symm, h2.symm⟩

lemma pw_injective {P : Ideal (𝓞 F)} (hP0 : P ≠ ⊥) {e e' : Exps} {y y' : Tup F}
    (hy : y ∈ CopP P) (hy' : y' ∈ CopP P) (h : pw P e y = pw P e' y') : e = e' ∧ y = y' := by
  obtain ⟨e1, e2, e3, e4⟩ := e
  obtain ⟨e1', e2', e3', e4'⟩ := e'
  obtain ⟨y1, y2, y3, y4⟩ := y
  obtain ⟨y1', y2', y3', y4'⟩ := y'
  simp only [pw, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := hy
  obtain ⟨b1, b2, b3, b4⟩ := hy'
  obtain ⟨c1, d1⟩ := cancel1 hP0 a1 b1 h1
  obtain ⟨c2, d2⟩ := cancel1 hP0 a2 b2 h2
  obtain ⟨c3, d3⟩ := cancel1 hP0 a3 b3 h3
  obtain ⟨c4, d4⟩ := cancel1 hP0 a4 b4 h4
  subst c1 c2 c3 c4 d1 d2 d3 d4
  exact ⟨rfl, rfl⟩

lemma exterior_of_dvd {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 (J * I)) : IsExterior 𝔪 I := by
  refine ⟨fun h => hI.1 (by rw [h, Ideal.mul_bot]), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right Ideal.mul_le_right _

lemma mem_Om_of_pw {𝔪 P : Ideal (𝓞 F)} {e : Exps} {y : Tup F} (h : pw P e y ∈ Om 𝔪) :
    y ∈ Om 𝔪 :=
  ⟨exterior_of_dvd h.1, exterior_of_dvd h.2.1, exterior_of_dvd h.2.2.1, exterior_of_dvd h.2.2.2⟩

lemma not_le_pw {P Q I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hQ : Q.IsPrime) (hPQ : P ≠ Q)
    (hI : ¬ I ≤ Q) (k : ℕ) : ¬ P ^ k * I ≤ Q := by
  intro h
  rcases hQ.mul_le.1 h with h1 | h1
  · exact hPQ (hP.eq_of_le hQ.ne_top (hQ.le_of_pow_le h1))
  · exact hI h1

lemma pw_mem_Cop {T : Finset (Ideal (𝓞 F))} (hT : ∀ Q ∈ T, Q.IsPrime) {P : Ideal (𝓞 F)}
    (hP : P.IsMaximal) (hPT : P ∉ T) (e : Exps) {y : Tup F} (hy : y ∈ Cop T) :
    pw P e y ∈ Cop T := by
  intro Q hQ
  have hPQ : P ≠ Q := fun h => hPT (h ▸ hQ)
  obtain ⟨a1, a2, a3, a4⟩ := hy Q hQ
  exact ⟨not_le_pw hP (hT Q hQ) hPQ a1 _, not_le_pw hP (hT Q hQ) hPQ a2 _,
    not_le_pw hP (hT Q hQ) hPQ a3 _, not_le_pw hP (hT Q hQ) hPQ a4 _⟩

lemma isEP_of_le {𝔪 P I : Ideal (𝓞 F)} (hP : P.IsMaximal) (hI : IsExterior 𝔪 I) (hle : I ≤ P) :
    IsEP 𝔪 P := by
  refine ⟨hP.isPrime, fun h => hI.1 (le_bot_iff.1 (h ▸ hle)), ?_⟩
  rw [eq_top_iff, ← hI.2]
  exact sup_le_sup_right hle _

/-- Decomposition of an exterior tuple at a prime. -/
lemma decomp4 {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {𝔪 : Ideal (𝓞 F)} {x : Tup F}
    (hx : x ∈ Om 𝔪) : ∃ e y, x = pw P e y ∧ y ∈ CopP P := by
  obtain ⟨k1, J1, h1, n1⟩ := decomp1 hP hP0 x.1 hx.1.1
  obtain ⟨k2, J2, h2, n2⟩ := decomp1 hP hP0 x.2.1 hx.2.1.1
  obtain ⟨k3, J3, h3, n3⟩ := decomp1 hP hP0 x.2.2.1 hx.2.2.1.1
  obtain ⟨k4, J4, h4, n4⟩ := decomp1 hP hP0 x.2.2.2 hx.2.2.2.1
  refine ⟨(k1, k2, k3, k4), (J1, J2, J3, J4), ?_, n1, n2, n3, n4⟩
  obtain ⟨x1, x2, x3, x4⟩ := x
  simp only [pw] at *
  rw [← h1, ← h2, ← h3, ← h4]

lemma le_of_pw (P : Ideal (𝓞 F)) (e : Exps) (y : Tup F) :
    (pw P e y).1 ≤ y.1 ∧ (pw P e y).2.1 ≤ y.2.1 ∧ (pw P e y).2.2.1 ≤ y.2.2.1 ∧
      (pw P e y).2.2.2 ≤ y.2.2.2 :=
  ⟨Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right, Ideal.mul_le_right⟩

lemma one4_mem_Cop (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime) :
    (one4 : Tup F) ∈ Cop T := by
  intro Q hQ
  have : ¬ (⊤ : Ideal (𝓞 F)) ≤ Q := fun h => (hT Q hQ).ne_top (top_le_iff.1 h)
  exact ⟨this, this, this, this⟩

section sieve

variable (𝔪 : Ideal (𝓞 F)) (f : Tup F → ℂ) (A : Ideal (𝓞 F) → Exps → ℂ)

/-- The hypotheses of the Euler product. -/
structure EulerHyp : Prop where
  zero : ∀ x, x ∉ Om 𝔪 → f x = 0
  one : f one4 = 1
  mul : ∀ P, IsEP 𝔪 P → ∀ e y, y ∈ Om 𝔪 → y ∈ CopP P → f (pw P e y) = A P e * f y
  summ : Summable (fun x => ‖f x‖)
  summA : ∀ P, IsEP 𝔪 P → Summable (fun e => ‖A P e‖)

variable {𝔪 f A}

lemma summable_norm_indicator (h : EulerHyp 𝔪 f A) (s : Set (Tup F)) :
    Summable (fun x => ‖s.indicator f x‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_indicator_le_norm_self _ _)
    h.summ

/-- One sieve step. -/
theorem sieve_step (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, Q.IsPrime)
    {P : Ideal (𝓞 F)} (hP : IsEP 𝔪 P) (hPT : P ∉ T) :
    ∑' x, (Cop T).indicator f x =
      (∑' e, A P e) * ∑' x, (Cop (insert P T)).indicator f x := by
  classical
  have hPmax : P.IsMaximal := hP.1.isMaximal hP.2.1
  set h1 := (Cop T).indicator f with hh1
  set h2 := (Cop (insert P T)).indicator f with hh2
  rw [tsum_mul_tsum_of_summable_norm (h.summA P hP) (summable_norm_indicator h _)]
  set G : Exps × Tup F → ℂ := fun z => A P z.1 * h2 z.2 with hG
  -- the key pointwise fact
  have hkey : ∀ z : Exps × Tup F, G z ≠ 0 →
      z.2 ∈ Cop (insert P T) ∧ z.2 ∈ Om 𝔪 ∧ h1 (pw P z.1 z.2) = G z := by
    intro z hz
    have hz2 : h2 z.2 ≠ 0 := fun h0 => hz (by simp [hG, h0])
    have hc : z.2 ∈ Cop (insert P T) := by
      by_contra hc; exact hz2 (Set.indicator_of_notMem hc _)
    have hO : z.2 ∈ Om 𝔪 := by
      by_contra hO; exact hz2 (by rw [hh2, Set.indicator_of_mem hc]; exact h.zero _ hO)
    refine ⟨hc, hO, ?_⟩
    have hcT : z.2 ∈ Cop T := fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)
    have hcP : z.2 ∈ CopP P := hc P (Finset.mem_insert_self _ _)
    rw [hh1, Set.indicator_of_mem (pw_mem_Cop hT hPmax hPT z.1 hcT), h.mul P hP z.1 z.2 hO hcP,
      hG]
    simp only
    rw [hh2, Set.indicator_of_mem hc]
  refine tsum_eq_tsum_of_ne_zero_bij (fun z => pw P z.1.1 z.1.2) ?_ ?_ ?_
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have a := (hkey z hz).1 P (Finset.mem_insert_self _ _)
    have b := (hkey z' hz').1 P (Finset.mem_insert_self _ _)
    obtain ⟨he, hy⟩ := pw_injective hP.2.1 a b hzz
    exact Subtype.ext (Prod.ext he hy)
  · intro x hx
    have hx' : h1 x ≠ 0 := hx
    have hxc : x ∈ Cop T := by
      by_contra hc; exact hx' (Set.indicator_of_notMem hc _)
    have hxO : x ∈ Om 𝔪 := by
      by_contra hO; exact hx' (by rw [hh1, Set.indicator_of_mem hxc]; exact h.zero _ hO)
    obtain ⟨e, y, rfl, hyP⟩ := decomp4 hP.1 hP.2.1 hxO
    have hyO : y ∈ Om 𝔪 := mem_Om_of_pw hxO
    have hyc : y ∈ Cop (insert P T) := by
      intro Q hQ
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      · exact hyP
      · obtain ⟨a1, a2, a3, a4⟩ := hxc Q hQ
        obtain ⟨l1, l2, l3, l4⟩ := le_of_pw P e y
        exact ⟨fun h' => a1 (l1.trans h'), fun h' => a2 (l2.trans h'),
          fun h' => a3 (l3.trans h'), fun h' => a4 (l4.trans h')⟩
    have hGe : G (e, y) = h1 (pw P e y) := by
      rw [hh1, Set.indicator_of_mem hxc, h.mul P hP e y hyO hyP, hG]
      simp only
      rw [hh2, Set.indicator_of_mem hyc]
    refine ⟨⟨(e, y), ?_⟩, rfl⟩
    show G (e, y) ≠ 0
    rw [hGe]; exact hx'
  · rintro ⟨z, hz⟩
    exact (hkey z hz).2.2

/-- The finite sieve. -/
theorem sieve_eq (h : EulerHyp 𝔪 f A) (T : Finset (Ideal (𝓞 F))) (hT : ∀ Q ∈ T, IsEP 𝔪 Q) :
    ∑' x, f x = (∏ Q ∈ T, ∑' e, A Q e) * ∑' x, (Cop T).indicator f x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : (Cop (∅ : Finset (Ideal (𝓞 F)))) = Set.univ := by
      ext x; simp [Cop]
    rw [this, Set.indicator_univ, Finset.prod_empty, one_mul]
  | insert P T hPT ih =>
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [ih', sieve_step h T (fun Q hQ => (hT Q (Finset.mem_insert_of_mem hQ)).1)
      (hT P (Finset.mem_insert_self _ _)) hPT, Finset.prod_insert hPT]
    ring

/-- The tail estimate. -/
theorem sieve_tail (h : EulerHyp 𝔪 f A) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : Finset (EP 𝔪), ∀ T : Finset (EP 𝔪), T₀ ⊆ T →
      ‖∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x - 1‖ < ε := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Tup F), ∑' x : {x // x ∉ S}, ‖f x‖ < ε :=
    ((tendsto_tsum_compl_atTop_zero (fun x => ‖f x‖)).eventually (gt_mem_nhds hε)).exists
  -- the coordinates of `S`
  set Sid : Finset (Ideal (𝓞 F)) := S.image (·.1) ∪ S.image (·.2.1) ∪ S.image (·.2.2.1) ∪
    S.image (·.2.2.2) with hSid
  have hfin : {P : EP 𝔪 | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P.1}.Finite := by
    have h1 : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P}.Finite := by
      have : {P : Ideal (𝓞 F) | ∃ I ∈ Sid, I ≠ ⊥ ∧ I ≤ P} ⊆
          ⋃ I ∈ Sid, {P : Ideal (𝓞 F) | Ideal.absNorm P ≤ Ideal.absNorm I} := by
        rintro P ⟨I, hI, hI0, hle⟩
        refine Set.mem_biUnion hI ?_
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
          (Ideal.absNorm_dvd_absNorm_of_le hle)
      exact (Set.Finite.biUnion Sid.finite_toSet fun I _ =>
        Ideal.finite_setOfPred_absNorm_le _).subset this
    exact h1.preimage (f := fun P : EP 𝔪 => P.1) Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, fun T hT => ?_⟩
  set T' := T.map (Function.Embedding.subtype _) with hT'
  have hT'p : ∀ Q ∈ T', Q.IsPrime := by
    intro Q hQ
    obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
    exact P.2.1
  -- inside `S`, only `one4` survives
  have hsurv : ∀ x ∈ S, x ∈ Cop T' → x ∈ Om 𝔪 → x = one4 := by
    intro x hxS hxc hxO
    have hcoord : ∀ I ∈ Sid, IsExterior 𝔪 I → (∀ Q ∈ T', ¬ I ≤ Q) → I = ⊤ := by
      intro I hI hIe hIc
      by_contra hIt
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hIt
      have hEP := isEP_of_le hM hIe hle
      have hmem : (⟨M, hEP⟩ : EP 𝔪) ∈ T := hT (by
        rw [Set.Finite.mem_toFinset]; exact ⟨I, hI, hIe.1, hle⟩)
      exact hIc M (Finset.mem_map.2 ⟨_, hmem, rfl⟩) hle
    have m1 : x.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image_of_mem _ hxS)))
    have m2 : x.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS)))
    have m3 : x.2.2.1 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image_of_mem _ hxS))
    have m4 : x.2.2.2 ∈ Sid := by
      simp only [hSid, Finset.mem_union]
      exact Or.inr (Finset.mem_image_of_mem _ hxS)
    have e1 := hcoord _ m1 hxO.1 fun Q hQ => (hxc Q hQ).1
    have e2 := hcoord _ m2 hxO.2.1 fun Q hQ => (hxc Q hQ).2.1
    have e3 := hcoord _ m3 hxO.2.2.1 fun Q hQ => (hxc Q hQ).2.2.1
    have e4 := hcoord _ m4 hxO.2.2.2 fun Q hQ => (hxc Q hQ).2.2.2
    obtain ⟨x1, x2, x3, x4⟩ := x
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]; rfl
  have hite : Summable (fun x : Tup F => if x = one4 then (1 : ℂ) else 0) :=
    (hasSum_ite_eq one4 (1 : ℂ)).summable
  have hpt : ∀ x, ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖ ≤
      ({x | x ∉ S} : Set (Tup F)).indicator (fun x => ‖f x‖) x := by
    intro x
    by_cases hx1 : x = one4
    · subst hx1
      rw [Set.indicator_of_mem (one4_mem_Cop T' hT'p), h.one, if_pos rfl, sub_self, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    rw [if_neg hx1, sub_zero]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_notMem (show x ∉ {x | x ∉ S} from fun h' => h' hxS)]
      by_cases hxc : x ∈ Cop T'
      · rw [Set.indicator_of_mem hxc]
        by_cases hxO : x ∈ Om 𝔪
        · exact absurd (hsurv x hxS hxc hxO) hx1
        · rw [h.zero x hxO, norm_zero]
      · rw [Set.indicator_of_notMem hxc, norm_zero]
    · rw [Set.indicator_of_mem (show x ∈ {x | x ∉ S} from hxS)]
      exact norm_indicator_le_norm_self _ _
  rw [← tsum_ite_eq (one4 : Tup F) (fun _ => (1 : ℂ)),
    ← ((summable_norm_indicator h _).of_norm).tsum_sub hite]
  have hsn : Summable (fun x => ‖(Cop T').indicator f x - (if x = one4 then (1 : ℂ) else 0)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (h.summ.indicator _)
  refine lt_of_le_of_lt (norm_tsum_le_tsum_norm hsn) ?_
  refine lt_of_le_of_lt (hsn.tsum_le_tsum hpt (h.summ.indicator _)) ?_
  rw [← tsum_subtype {x | x ∉ S} (fun x => ‖f x‖)]
  exact hS

/-- **The Euler product.** -/
theorem euler4 (h : EulerHyp 𝔪 f A) :
    HasProd (fun P : EP 𝔪 => ∑' e, A P.1 e) (∑' x, f x) ∧
      ((∀ P : EP 𝔪, ∑' e, A P.1 e ≠ 0) → ∑' x, f x ≠ 0) := by
  classical
  set X := ∑' x, f x
  set S : Finset (EP 𝔪) → ℂ :=
    fun T => ∑' x, (Cop (T.map (Function.Embedding.subtype _))).indicator f x with hSdef
  have hEq : ∀ T : Finset (EP 𝔪), X = (∏ P ∈ T, ∑' e, A P.1 e) * S T := by
    intro T
    have := sieve_eq h (T.map (Function.Embedding.subtype _)) (by
      intro Q hQ
      obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
      exact P.2)
    rw [Finset.prod_map] at this
    exact this
  have hS1 : Tendsto S atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := sieve_tail h hε
    exact ⟨T₀, fun T hT => by rw [dist_eq_norm]; exact hT₀ T hT⟩
  constructor
  · have hev : ∀ᶠ T in atTop, ∏ P ∈ T, ∑' e, A P.1 e = X / S T := by
      filter_upwards [hS1.eventually_ne one_ne_zero] with T hT
      rw [hEq T, mul_div_assoc, div_self hT, mul_one]
    show Tendsto _ (SummationFilter.unconditional _).filter _
    simp only [SummationFilter.unconditional_filter]
    have : Tendsto (fun T => X / S T) atTop (𝓝 (X / 1)) := tendsto_const_nhds.div hS1 one_ne_zero
    rw [div_one] at this
    exact this.congr' (hev.mono fun T hT => hT.symm)
  · intro hne hX
    obtain ⟨T, hT⟩ := (hS1.eventually_ne one_ne_zero).exists
    have := hEq T
    rw [hX] at this
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P _ => hne P) hT this.symm

/-- The size `N x₁ N x₂ N x₃ N x₄` of a tuple. -/
noncomputable def mu (x : Tup F) : ℕ :=
  Ideal.absNorm x.1 * Ideal.absNorm x.2.1 * Ideal.absNorm x.2.2.1 * Ideal.absNorm x.2.2.2

lemma pw_zero (P : Ideal (𝓞 F)) (y : Tup F) : pw P (0, 0, 0, 0) y = y := by
  obtain ⟨y1, y2, y3, y4⟩ := y
  simp [pw]

lemma mu_pw (P : Ideal (𝓞 F)) (e : Exps) (y : Tup F) :
    mu (pw P e y) = Ideal.absNorm P ^ (e.1 + e.2.1 + e.2.2.1 + e.2.2.2) * mu y := by
  simp only [mu, pw, map_mul, map_pow, pow_add]
  ring

/-- Multiplicative majorants. -/
theorem norm_le_of_mul {𝔪 : Ideal (𝓞 F)} (f : Tup F → ℂ) (A : Ideal (𝓞 F) → Exps → ℂ)
    (B : Tup F → ℝ) (β : Ideal (𝓞 F) → Exps → ℝ)
    (hmul : ∀ P, IsEP 𝔪 P → ∀ e y, y ∈ Om 𝔪 → y ∈ CopP P → f (pw P e y) = A P e * f y)
    (hB : ∀ P, IsEP 𝔪 P → ∀ e y, B (pw P e y) = β P e * B y)
    (hAβ : ∀ P, IsEP 𝔪 P → ∀ e, ‖A P e‖ ≤ β P e)
    (h1 : ‖f one4‖ ≤ B one4) : ∀ x ∈ Om 𝔪, ‖f x‖ ≤ B x := by
  intro x
  induction hN : mu x using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  intro hx
  by_cases hx1 : x = one4
  · subst hx1; exact h1
  obtain ⟨I, hIx, hIt⟩ : ∃ I, (I = x.1 ∨ I = x.2.1 ∨ I = x.2.2.1 ∨ I = x.2.2.2) ∧ I ≠ ⊤ := by
    by_contra hc
    push Not at hc
    apply hx1
    obtain ⟨x1, x2, x3, x4⟩ := x
    simp only at hc
    rw [hc x1 (Or.inl rfl), hc x2 (Or.inr (Or.inl rfl)), hc x3 (Or.inr (Or.inr (Or.inl rfl))),
      hc x4 (Or.inr (Or.inr (Or.inr rfl)))]
    rfl
  have hIe : IsExterior 𝔪 I := by
    rcases hIx with rfl | rfl | rfl | rfl
    exacts [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hIt
  have hEP := isEP_of_le hM hIe hle
  obtain ⟨e, y, rfl, hyM⟩ := decomp4 hEP.1 hEP.2.1 hx
  have hyO : y ∈ Om 𝔪 := mem_Om_of_pw hx
  have hsum : 1 ≤ e.1 + e.2.1 + e.2.2.1 + e.2.2.2 := by
    by_contra hc
    have he : e = (0, 0, 0, 0) := by
      obtain ⟨e1, e2, e3, e4⟩ := e
      simp only at hc
      have : e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0 := by omega
      obtain ⟨rfl, rfl, rfl, rfl⟩ := this
      rfl
    subst he
    rw [pw_zero] at hIx
    obtain ⟨a1, a2, a3, a4⟩ := hyM
    rcases hIx with rfl | rfl | rfl | rfl
    exacts [a1 hle, a2 hle, a3 hle, a4 hle]
  have hmu0 : 0 < mu y := by
    have n : ∀ J : Ideal (𝓞 F), IsExterior 𝔪 J → 0 < Ideal.absNorm J := fun J hJ =>
      Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ.1)
    simp only [mu]
    have := n _ hyO.1; have := n _ hyO.2.1; have := n _ hyO.2.2.1; have := n _ hyO.2.2.2
    positivity
  have hlt : mu y < N := by
    rw [← hN, mu_pw]
    have h2 : 2 ≤ Ideal.absNorm M ^ (e.1 + e.2.1 + e.2.2.1 + e.2.2.2) :=
      (two_le_absNorm hEP.1 hEP.2.1).trans (Nat.le_self_pow (by omega) _)
    nlinarith
  have ihy := ih _ hlt y rfl hyO
  rw [hmul M hEP e y hyO hyM, hB M hEP e y, norm_mul]
  exact mul_le_mul (hAβ M hEP e) ihy (norm_nonneg _) ((norm_nonneg _).trans (hAβ M hEP e))

end sieve

end C3A

end ArtinPrimitiveRoots
end

section
/-! # C3A_Local: the local coefficients of the principal frequency series and their sum

`principalLocalCoeff Q η θ e₀ l k m` is the coefficient of the principal row `ℱ₁` at a prime `𝔭`
of norm `Q`, for `v_𝔭(𝔠) = e₀ ∈ {0,1}`, `v_𝔭(𝔫) = l`, `v_𝔭(𝔰) = k`, `v_𝔭(𝔯) = m`
(Prop 7.3, (7.16)–(7.17) at `u = 1`, `t = e₀ + 3l`, `J = 6m`): with `η = η(𝔭)` and
`θ = ϑ(𝔭)⁶`, and `γ₁γ₂ϑ = −η`, `τ₁ = √Q γ₁`, `τ₁τ₅ = Q` substituted,

* `t = 0`: `1` if `k = 0` or `m = 0`;
* `t = 6d`, `d ≥ 1`: `θ^d Q^{6d}(1 − Q⁻¹)` if `k = 0`, `m ≥ d`; `θ^d Q^{6d}` if `k = 1`, `m = d`;
* `t = 6d + 1`: `−η √Q θ^d Q^{6d}` if `k = 0`, `m = d`; `−η √Q θ^d Q^{6d} (Q − 1)` if `k = 1`, `m > d`;
* `0` otherwise.

`hasSum_local`: weighted by `wc^{e₀} wn^l ws^k wr^m`, the coefficients sum to the closed form (7.19). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

/-- The local coefficient (7.16)–(7.17) of the principal row at `u = 1`. -/
noncomputable def principalLocalCoeff (Q : ℕ) (η θ : ℂ) (e₀ l k m : ℕ) : ℂ :=
  if e₀ = 0 then
    if l = 0 then (if k = 0 ∨ m = 0 then 1 else 0)
    else if Even l then
      (if k = 0 ∧ l / 2 ≤ m then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * (1 - (Q : ℂ)⁻¹)
       else if k = 1 ∧ m = l / 2 then θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) else 0)
    else 0
  else if e₀ = 1 ∧ Even l then
    (if k = 0 ∧ m = l / 2 then -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l)
     else if k = 1 ∧ l / 2 < m then
       -(η * (Real.sqrt Q : ℂ)) * θ ^ (l / 2) * (Q : ℂ) ^ (3 * l) * ((Q : ℂ) - 1)
     else 0)
  else 0

/-- The index set of the six geometric families. -/
abbrev Dom : Type := ℕ ⊕ ℕ ⊕ (ℕ × ℕ) ⊕ ℕ ⊕ ℕ ⊕ (ℕ × ℕ)

/-- The six geometric families of exponents. -/
def phi : Dom → Exps
  | .inl m => (0, 0, 0, m)
  | .inr (.inl k) => (0, 0, k + 1, 0)
  | .inr (.inr (.inl (d, j))) => (0, 2 * d + 2, 0, d + 1 + j)
  | .inr (.inr (.inr (.inl d))) => (0, 2 * d + 2, 1, d + 1)
  | .inr (.inr (.inr (.inr (.inl d)))) => (1, 2 * d, 0, d)
  | .inr (.inr (.inr (.inr (.inr (d, j))))) => (1, 2 * d, 1, d + 1 + j)

lemma phi_injective : Function.Injective phi := by
  intro a b h
  rcases a with m | k | ⟨d, j⟩ | d | d | ⟨d, j⟩ <;>
  rcases b with m' | k' | ⟨d', j'⟩ | d' | d' | ⟨d', j'⟩ <;>
  simp [phi] at h ⊢ <;> omega

lemma coeff_eq_zero_of_notMem (Q : ℕ) (η θ : ℂ) (e : Exps) (he : e ∉ Set.range phi) :
    principalLocalCoeff Q η θ e.1 e.2.1 e.2.2.1 e.2.2.2 = 0 := by
  obtain ⟨e0, l, k, m⟩ := e
  simp only [Set.mem_range, not_exists] at he
  simp only
  unfold principalLocalCoeff
  by_cases h0 : e0 = 0
  · subst h0
    rw [if_pos rfl]
    by_cases hl : l = 0
    · subst hl
      rw [if_pos rfl]
      by_cases hk : k = 0
      · subst hk; exact (he (.inl m) rfl).elim
      by_cases hm : m = 0
      · subst hm
        exact (he (.inr (.inl (k - 1))) (by simp only [phi, Prod.mk.injEq, true_and, and_true]; omega)).elim
      rw [if_neg (by omega)]
    rw [if_neg hl]
    by_cases hev : Even l
    · rw [if_pos hev]
      have h2 : l % 2 = 0 := Nat.even_iff.1 hev
      by_cases c1 : k = 0 ∧ l / 2 ≤ m
      · exact (he (.inr (.inr (.inl (l / 2 - 1, m - l / 2)))) (by simp only [phi, Prod.mk.injEq, true_and, and_true]; omega)).elim
      rw [if_neg c1]
      by_cases c2 : k = 1 ∧ m = l / 2
      · exact (he (.inr (.inr (.inr (.inl (l / 2 - 1))))) (by simp only [phi, Prod.mk.injEq, true_and, and_true]; omega)).elim
      rw [if_neg c2]
    · rw [if_neg hev]
  · rw [if_neg h0]
    by_cases h1 : e0 = 1 ∧ Even l
    · rw [if_pos h1]
      have h2 : l % 2 = 0 := Nat.even_iff.1 h1.2
      by_cases c1 : k = 0 ∧ m = l / 2
      · exact (he (.inr (.inr (.inr (.inr (.inl (l / 2)))))) (by simp only [phi, Prod.mk.injEq, true_and, and_true]; omega)).elim
      rw [if_neg c1]
      by_cases c2 : k = 1 ∧ l / 2 < m
      · exact (he (.inr (.inr (.inr (.inr (.inr (l / 2, m - l / 2 - 1)))))) (by simp only [phi, Prod.mk.injEq, true_and, and_true]; omega)).elim
      rw [if_neg c2]
    · rw [if_neg h1]

section sum

variable (Q : ℕ) (η θ wc wn ws wr : ℂ)

/-- The weighted local coefficient. -/
noncomputable def locTerm (e : Exps) : ℂ :=
  principalLocalCoeff Q η θ e.1 e.2.1 e.2.2.1 e.2.2.2 * wc ^ e.1 * wn ^ e.2.1 * ws ^ e.2.2.1 *
    wr ^ e.2.2.2

/-- The closed form (7.19), with `V = wr`, `W = ws`, `D = η √Q wc`, `E = θ Q⁶ wn² wr`. -/
noncomputable def locSum : ℂ :=
  let V := wr
  let W := ws
  let D := η * (Real.sqrt Q : ℂ) * wc
  let E := θ * (Q : ℂ) ^ 6 * wn ^ 2 * wr
  (1 - V)⁻¹ + W * (1 - W)⁻¹ + E * (1 - E)⁻¹ * ((1 - (Q : ℂ)⁻¹) * (1 - V)⁻¹) +
    E * (1 - E)⁻¹ * W + (-D) * (1 - E)⁻¹ + (-D) * (1 - E)⁻¹ * (((Q : ℂ) - 1) * W * (V * (1 - V)⁻¹))

lemma hasSum_prod_geom {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (a b : ℂ) :
    HasSum (fun p : ℕ × ℕ => (a * x ^ p.1) * (b * y ^ p.2)) ((a * (1 - x)⁻¹) * (b * (1 - y)⁻¹)) := by
  have h1 : HasSum (fun n : ℕ => a * x ^ n) (a * (1 - x)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hx).mul_left a
  have h2 : HasSum (fun n : ℕ => b * y ^ n) (b * (1 - y)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hy).mul_left b
  have s1 : Summable (fun n : ℕ => ‖a * x ^ n‖) :=
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖a‖).congr fun n => by
      rw [norm_mul, norm_pow]
  have s2 : Summable (fun n : ℕ => ‖b * y ^ n‖) :=
    ((summable_geometric_of_lt_one (norm_nonneg y) hy).mul_left ‖b‖).congr fun n => by
      rw [norm_mul, norm_pow]
  have s3 : Summable (fun p : ℕ × ℕ => (a * x ^ p.1) * (b * y ^ p.2)) :=
    summable_mul_of_summable_norm (R := ℂ) (f := fun n : ℕ => a * x ^ n)
      (g := fun n : ℕ => b * y ^ n) s1 s2
  exact HasSum.mul (f := fun n : ℕ => a * x ^ n) (g := fun n : ℕ => b * y ^ n) h1 h2 s3

theorem hasSum_local (hV : ‖wr‖ < 1) (hW : ‖ws‖ < 1)
    (hE : ‖θ * (Q : ℂ) ^ 6 * wn ^ 2 * wr‖ < 1) :
    HasSum (locTerm Q η θ wc wn ws wr) (locSum Q η θ wc wn ws wr) := by
  set E := θ * (Q : ℂ) ^ 6 * wn ^ 2 * wr with hEdef
  set D := η * (Real.sqrt Q : ℂ) * wc with hDdef
  rw [← (phi_injective.hasSum_iff (fun e he => by
    simp only [locTerm, coeff_eq_zero_of_notMem Q η θ e he, zero_mul]))]
  have g1 := hasSum_geometric_of_norm_lt_one hV
  have g2 := (hasSum_geometric_of_norm_lt_one hW).mul_left ws
  have g3 := hasSum_prod_geom hE hV E ((1 - (Q : ℂ)⁻¹))
  have g4 := ((hasSum_geometric_of_norm_lt_one hE).mul_left E).mul_right ws
  have g5 := (hasSum_geometric_of_norm_lt_one hE).mul_left (-D)
  have g6 := hasSum_prod_geom hE hV (-D) (((Q : ℂ) - 1) * ws * wr)
  have hsq : ∀ d : ℕ, (2 * d + 2) / 2 = d + 1 := fun d => by omega
  have hsq' : ∀ d : ℕ, (2 * d) / 2 = d := fun d => by omega
  have hev : ∀ d : ℕ, Even (2 * d + 2) := fun d => ⟨d + 1, by ring⟩
  have hev' : ∀ d : ℕ, Even (2 * d) := fun d => ⟨d, by ring⟩
  have hsplit : locSum Q η θ wc wn ws wr = (1 - wr)⁻¹ + (ws * (1 - ws)⁻¹ +
      ((E * (1 - E)⁻¹) * ((1 - (Q : ℂ)⁻¹) * (1 - wr)⁻¹) + (E * (1 - E)⁻¹ * ws +
      ((-D) * (1 - E)⁻¹ + (-D) * (1 - E)⁻¹ * ((((Q : ℂ) - 1) * ws * wr) * (1 - wr)⁻¹))))) := by
    unfold locSum
    simp only [hEdef, hDdef]
    ring
  rw [hsplit]
  refine HasSum.sum ?_ (HasSum.sum ?_ (HasSum.sum ?_ (HasSum.sum ?_ (HasSum.sum ?_ ?_))))
  · refine g1.congr_fun fun m => ?_
    simp [locTerm, phi, principalLocalCoeff]
  · refine g2.congr_fun fun k => ?_
    simp [locTerm, phi, principalLocalCoeff]
    ring
  · refine g3.congr_fun fun p => ?_
    obtain ⟨d, j⟩ := p
    show locTerm Q η θ wc wn ws wr (0, 2 * d + 2, 0, d + 1 + j) = _
    simp only [locTerm]
    rw [principalLocalCoeff, if_pos rfl, if_neg (by omega : 2 * d + 2 ≠ 0), if_pos (hev d),
      if_pos (⟨rfl, by omega⟩ : (0 : ℕ) = 0 ∧ (2 * d + 2) / 2 ≤ d + 1 + j), hsq, hEdef]
    ring
  · refine g4.congr_fun fun d => ?_
    show locTerm Q η θ wc wn ws wr (0, 2 * d + 2, 1, d + 1) = _
    simp only [locTerm]
    rw [principalLocalCoeff, if_pos rfl, if_neg (by omega : 2 * d + 2 ≠ 0), if_pos (hev d),
      if_neg (by omega : ¬ ((1 : ℕ) = 0 ∧ (2 * d + 2) / 2 ≤ d + 1)),
      if_pos (⟨rfl, by omega⟩ : (1 : ℕ) = 1 ∧ d + 1 = (2 * d + 2) / 2), hsq, hEdef]
    ring
  · refine g5.congr_fun fun d => ?_
    show locTerm Q η θ wc wn ws wr (1, 2 * d, 0, d) = _
    simp only [locTerm]
    rw [principalLocalCoeff, if_neg one_ne_zero, if_pos (⟨rfl, hev' d⟩ : (1 : ℕ) = 1 ∧ Even (2 * d)),
      if_pos (⟨rfl, by omega⟩ : (0 : ℕ) = 0 ∧ d = 2 * d / 2), hsq', hEdef, hDdef]
    ring
  · refine g6.congr_fun fun p => ?_
    obtain ⟨d, j⟩ := p
    show locTerm Q η θ wc wn ws wr (1, 2 * d, 1, d + 1 + j) = _
    simp only [locTerm]
    rw [principalLocalCoeff, if_neg one_ne_zero, if_pos (⟨rfl, hev' d⟩ : (1 : ℕ) = 1 ∧ Even (2 * d)),
      if_neg (by omega : ¬ ((1 : ℕ) = 0 ∧ d + 1 + j = 2 * d / 2)),
      if_pos (⟨rfl, by omega⟩ : (1 : ℕ) = 1 ∧ 2 * d / 2 < d + 1 + j), hsq', hEdef, hDdef]
    ring

end sum

end C3A

end ArtinPrimitiveRoots
end

section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-- `g_s(I) = χ(I) N(I)^{-s}`. -/
noncomputable def gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  χ.toFun I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)

theorem gs_mul {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) (I J : Ideal (𝓞 F)) :
    gs χ s (I * J) = gs χ s I * gs χ s J := by
  simp only [gs, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, χ.map_mul']
  ring

theorem gs_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊥ = 0 := by
  simp [gs, toFun_bot]

theorem gs_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ) : gs χ s ⊤ = 1 := by
  simp [gs, toFun_top]

theorem norm_gs_le {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) (I : Ideal (𝓞 F)) :
    ‖gs χ s I‖ ≤ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ) := by
  by_cases hI : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff.1 hI, gs_bot, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  rw [gs, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hI), Complex.neg_re]
  calc ‖χ.toFun I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
      ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-σ) :=
        mul_le_mul (hχ I) (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := one_mul _

theorem summable_gs {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (gs χ s) :=
  Summable.of_norm_bounded (summable_absNorm_rpow hs) (norm_gs_le χ hχ le_rfl)

/-- `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` on `Re s > 1`. -/
theorem lseries_eq_tsum {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : χ.LSeries s = ∑' I, gs χ s I := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hsum := summable_gs χ hχ hs
  have hs2 : Summable (fun p => gs χ s (e p)) := (e.summable_iff).2 hsum
  rw [← e.tsum_eq, hs2.tsum_sigma, HeckeChar.LSeries, LSeries]
  congr 1
  funext n
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      gs χ s (e ⟨n, y⟩) = χ.toFun y.1 * (n : ℂ) ^ (-s) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, gs, y.2]
  simp only [hfib]
  rw [tsum_mul_right]
  have hcoeff : (∑' y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, χ.toFun y.1) = χ.coeff n := by
    rw [HeckeChar.coeff, finsum_mem_def,
      ← tsum_eq_finsum (L := SummationFilter.unconditional (Ideal (𝓞 F)))
        ((Ideal.finite_setOfPred_absNorm_eq n).subset
        Set.support_indicator_subset),
      ← tsum_subtype]
    rfl
  rw [hcoeff]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow, mul_zero]
    intro h
    have : s = 0 := neg_eq_zero.1 h
    rw [this, Complex.zero_re] at hs
    linarith
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-! ### The finite sieve -/

/-- The ideals not contained in any member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F)) := {I | ∀ P ∈ T, ¬ I ≤ P}

theorem sieve (g : Ideal (𝓞 F) → ℂ) (hmul : ∀ I J, g (I * J) = g I * g J) (hg : Summable g)
    (T : Finset (Ideal (𝓞 F))) (hT : ∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥) :
    (∑' I, g I) * ∏ P ∈ T, (1 - g P) = ∑' I, (Cop T).indicator g I := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cop]
  | insert P T hPT ih =>
    have hP := hT P (Finset.mem_insert_self P T)
    have ih' := ih (fun Q hQ => hT Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.prod_insert hPT, mul_left_comm, mul_comm, ih']
    set h := (Cop T).indicator g with hh
    have hhs : Summable h := hg.indicator _
    have hPI : ∀ I, h (P * I) = g P * h I := by
      intro I
      by_cases hI : I ∈ Cop T
      · have hPI' : P * I ∈ Cop T := by
          intro Q hQ hle
          rcases (hT Q (Finset.mem_insert_of_mem hQ)).1.mul_le.1 hle with h1 | h1
          · have := (hP.1.isMaximal hP.2).eq_of_le (hT Q (Finset.mem_insert_of_mem hQ)).1.ne_top h1
            exact hPT (this ▸ hQ)
          · exact hI Q hQ h1
        rw [hh, Set.indicator_of_mem hPI', Set.indicator_of_mem hI, hmul]
      · have hPI' : P * I ∉ Cop T := by
          intro hc
          simp only [Cop, Set.mem_setOf_eq, not_forall, not_not] at hI
          obtain ⟨Q, hQ, hle⟩ := hI
          exact hc Q hQ (Ideal.mul_le_right.trans hle)
        rw [hh, Set.indicator_of_notMem hPI', Set.indicator_of_notMem hI, mul_zero]
    have hshift : g P * ∑' I, h I = ∑' J, {J | J ≤ P}.indicator h J := by
      rw [← hhs.tsum_mul_left]
      have hinj : Function.Injective (fun I : Ideal (𝓞 F) => P * I) := by
        intro a b hab
        have hP0 : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP.2
        exact mul_left_cancel₀ hP0 hab
      rw [← hinj.tsum_eq (f := {J | J ≤ P}.indicator h)]
      · congr 1
        funext I
        rw [Set.indicator_of_mem (show P * I ∈ {J | J ≤ P} from Ideal.mul_le_left), hPI]
      · intro J hJ
        have hle : J ≤ P := by
          by_contra hc
          exact hJ (Set.indicator_of_notMem hc _)
        obtain ⟨c, rfl⟩ := Ideal.dvd_iff_le.2 hle
        exact ⟨c, rfl⟩
    rw [mul_sub, mul_one, mul_comm, hshift, ← hhs.tsum_sub (hhs.indicator _)]
    congr 1
    funext J
    simp only [hh, Set.indicator, Cop, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp]
    by_cases h1 : J ≤ P <;> by_cases h2 : ∀ Q ∈ T, ¬J ≤ Q <;> simp [h1, h2]

end T12B

end ArtinPrimitiveRoots
end

section
/-! # C3A_Euler1: Euler products of `L(s, χ)` and `ζ^S(s)` over the exterior primes

From `euler4` (one active coordinate) and T12B's sieve:
* `hasProd_inv_LSeries`: `∏_{P ∉ S} (1 − χ(P) N P^{-s}) = L(s, χ)⁻¹` for `Re s > 1`;
* `hasProd_zetaS`: `∏_{P ∉ S} (1 − N P^{-s})⁻¹ = ∏_{P ⊇ 𝔪} (1 − N P^{-s}) · ζ_F(s)`. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

lemma sup_mul_eq_top_iff {𝔪 I J : Ideal (𝓞 F)} :
    I * J ⊔ 𝔪 = ⊤ ↔ I ⊔ 𝔪 = ⊤ ∧ J ⊔ 𝔪 = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_left _
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_right _
  · rintro ⟨h1, h2⟩
    rw [Ideal.mul_sup_eq_of_coprime_left h1, h2]

/-- The trivial Hecke character modulo `𝔪`. -/
noncomputable def trivChar (𝔪 : Ideal (𝓞 F)) : HeckeChar F 𝔪 where
  toFun I := by classical exact if I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then 1 else 0
  map_mul' I J := by
    classical
    have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
      simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ <;> by_cases hJ : J ≠ ⊥ ∧ J ⊔ 𝔪 = ⊤
    · rw [if_pos ⟨hb.2 ⟨hI.1, hJ.1⟩, sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩, if_pos hI, if_pos hJ,
        mul_one]
    · rw [if_neg hJ, mul_zero, if_neg]
      rintro ⟨h1, h2⟩; exact hJ ⟨(hb.1 h1).2, (sup_mul_eq_top_iff.1 h2).2⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (sup_mul_eq_top_iff.1 h2).1⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (sup_mul_eq_top_iff.1 h2).1⟩
  eq_zero_iff' I := by
    classical
    by_cases h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤
    · simp only [if_pos h, one_ne_zero, false_iff, not_or, not_not]; exact h
    · simp only [if_neg h, true_iff]
      by_contra h'
      push Not at h'
      exact h h'
  map_principal' α hα h1 := by
    classical
    have hspan : Ideal.span {α} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    have hcop : Ideal.span {α} ⊔ 𝔪 = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have : (1 : 𝓞 F) = α - (α - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
        (Ideal.mem_sup_right h1)
    simp only [if_pos (⟨hspan, hcop⟩ : Ideal.span {α} ≠ ⊥ ∧ Ideal.span {α} ⊔ 𝔪 = ⊤)]

lemma trivChar_apply {𝔪 I : Ideal (𝓞 F)} (h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤) : (trivChar 𝔪).toFun I = 1 := by
  classical
  simp only [trivChar]
  convert if_pos h

lemma trivChar_norm_le (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) : ‖(trivChar 𝔪).toFun I‖ ≤ 1 := by
  classical
  simp only [trivChar]
  split_ifs <;> simp

/-! ### The one-variable Euler product from `euler4` -/

section one

variable {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ)

/-- The function `χ(I) N I^{-s}` placed on the first coordinate. -/
noncomputable def f1 (x : Tup F) : ℂ := by
  classical exact if x.2 = (⊤, ⊤, ⊤) then T12B.gs χ s x.1 else 0

/-- Its local factors. -/
noncomputable def A1 (P : Ideal (𝓞 F)) (e : Exps) : ℂ := by
  classical exact if e.2 = (0, 0, 0) then T12B.gs χ s P ^ e.1 else 0

lemma pow_mul_eq_top {P I : Ideal (𝓞 F)} (hP : P.IsPrime) {k : ℕ} :
    P ^ k * I = ⊤ ↔ k = 0 ∧ I = ⊤ := by
  constructor
  · intro h
    rcases k with _ | k
    · simp only [pow_zero, one_mul] at h; exact ⟨rfl, h⟩
    · exfalso; apply hP.ne_top
      rw [eq_top_iff, ← h, pow_succ', mul_assoc]; exact Ideal.mul_le_left
  · rintro ⟨rfl, rfl⟩; simp

theorem euler1 (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun P : EP 𝔪 => (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      (χ.LSeries s) ∧ χ.LSeries s ≠ 0 := by
  classical
  have hg : ∀ P : Ideal (𝓞 F), IsEP 𝔪 P → ‖T12B.gs χ s P‖ < 1 := by
    intro P hP
    have h2 := two_le_absNorm hP.1 hP.2.1
    refine lt_of_le_of_lt (T12B.norm_gs_le χ hχ (le_refl s.re) P) ?_
    have hq : (1 : ℝ) < ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast h2
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hinj : Function.Injective (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro a b h; simpa using h
  have hsupp : Function.support (f1 χ s) ⊆ Set.range (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) := by
    intro x hx
    simp only [Function.mem_support, f1] at hx
    split_ifs at hx with h
    swap
    · exact absurd rfl hx
    obtain ⟨x1, x2⟩ := x
    simp only at h
    exact ⟨x1, by rw [h]⟩
  have hcomp : (f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) = T12B.gs χ s := by
    funext c; simp [f1]
  have hsumm : Summable (T12B.gs χ s) := T12B.summable_gs χ hχ hs
  have hH : EulerHyp 𝔪 (f1 χ s) (A1 χ s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [f1]
      split_ifs with h
      · obtain ⟨x1, x2⟩ := x
        simp only at h
        subst h
        have : ¬ IsExterior 𝔪 x1 := fun h' => hx ⟨h', ⟨top_ne_bot, top_sup_eq _⟩,
          ⟨top_ne_bot, top_sup_eq _⟩, ⟨top_ne_bot, top_sup_eq _⟩⟩
        simp only [T12B.gs]
        rw [(χ.eq_zero_iff' x1).2 (by
          by_contra hc; push Not at hc; exact this hc), zero_mul]
      · rfl
    · simp [f1, one4, T12B.gs_top]
    · intro P hP e y hyO hyP
      obtain ⟨e1, e2, e3, e4⟩ := e
      obtain ⟨y1, y2, y3, y4⟩ := y
      simp only [f1, A1, pw, Prod.mk.injEq]
      by_cases he : e2 = 0 ∧ e3 = 0 ∧ e4 = 0
      · obtain ⟨rfl, rfl, rfl⟩ := he
        simp only [pow_zero, one_mul, and_self, if_true]
        split_ifs
        · have hpow : T12B.gs χ s (P ^ e1) = T12B.gs χ s P ^ e1 := by
            induction e1 with
            | zero => simp [T12B.gs_top]
            | succ k ih => rw [pow_succ, T12B.gs_mul, ih, pow_succ]
          rw [T12B.gs_mul, hpow]
        · rw [mul_zero]
      · rw [if_neg, if_neg he, zero_mul]
        rintro ⟨h2, h3, h4⟩
        rw [pow_mul_eq_top hP.1] at h2 h3 h4
        exact he ⟨h2.1, h3.1, h4.1⟩
    · rw [← hinj.summable_iff (fun x hx => by
        by_contra h; exact hx (hsupp (norm_ne_zero_iff.1 h)))]
      rw [show (fun x => ‖f1 χ s x‖) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F)) =
        fun c => ‖T12B.gs χ s c‖ by rw [← hcomp]; rfl]
      exact Summable.of_norm_bounded (T12B.summable_absNorm_rpow hs)
        (fun c => by rw [norm_norm]; exact T12B.norm_gs_le χ hχ le_rfl c)
    · intro P hP
      have hgeo := summable_geometric_of_lt_one (norm_nonneg _) (hg P hP)
      have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
        intro a b h; simpa using h
      rw [← hinj'.summable_iff (fun e he => by
        obtain ⟨e1, e2⟩ := e
        simp only [A1]
        rw [if_neg, norm_zero]
        intro h; exact he ⟨e1, by rw [h]⟩)]
      refine hgeo.congr fun k => ?_
      simp [A1]
  obtain ⟨hprod, hne⟩ := euler4 hH
  have htsum : ∑' x, f1 χ s x = χ.LSeries s := by
    rw [← hinj.tsum_eq hsupp]
    show ∑' c, ((f1 χ s) ∘ (fun c : Ideal (𝓞 F) => ((c, ⊤, ⊤, ⊤) : Tup F))) c = _
    rw [hcomp, T12B.lseries_eq_tsum χ hχ hs]
  have hloc : ∀ P : EP 𝔪, ∑' e, A1 χ s P.1 e =
      (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
    intro P
    have hinj' : Function.Injective (fun k : ℕ => ((k, 0, 0, 0) : Exps)) := by
      intro a b h; simpa using h
    rw [← hinj'.tsum_eq (fun e he => by
      obtain ⟨e1, e2⟩ := e
      simp only [Function.mem_support, A1] at he
      split_ifs at he with h'
      · exact ⟨e1, by rw [h']⟩
      · exact absurd rfl he)]
    simp only [A1, if_true]
    exact tsum_geometric_of_norm_lt_one (hg P.1 P.2)
  rw [htsum] at hprod hne
  refine ⟨?_, ?_⟩
  · exact hprod.congr_fun fun P => (hloc P).symm
  · refine hne fun P => ?_
    rw [hloc P]
    refine inv_ne_zero fun h => ?_
    have := hg P.1 P.2
    rw [sub_eq_zero] at h
    have h' : T12B.gs χ s P.1 = 1 := h.symm
    rw [h', norm_one] at this
    exact lt_irrefl _ this

end one

/-! ### `ζ^S` -/

lemma dedekindZeta_eq_LSeries_trivChar (s : ℂ) :
    dedekindZeta F s = (trivChar (⊤ : Ideal (𝓞 F))).LSeries s := by
  classical
  unfold dedekindZeta HeckeChar.LSeries
  refine LSeries_congr (fun {n} hn => ?_) s
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
  unfold HeckeChar.coeff
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) (fun I hI => by
    rw [Set.Finite.mem_toFinset] at hI
    refine trivChar_apply ⟨?_, sup_top_eq _⟩
    rintro rfl
    simp at hI
    exact hn hI.symm)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact Nat.card_eq_card_finite_toFinset hfin

lemma finite_primes_ge {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪)).subset ?_
  intro P ⟨_, _, hle'⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle')

lemma LSeries_trivChar {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    (trivChar 𝔪).LSeries s =
      (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
        (1 - (Ideal.absNorm P : ℂ) ^ (-s))) * dedekindZeta F s := by
  classical
  have hfin := finite_primes_ge h𝔪
  set T := hfin.toFinset with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P := fun P => by simp [hT]
  set g := T12B.gs (trivChar (⊤ : Ideal (𝓞 F))) s
  have hsv := T12B.sieve g (T12B.gs_mul _ s) (T12B.summable_gs _ (trivChar_norm_le _) hs) T
    (fun P hP => ⟨((hTmem P).1 hP).1, ((hTmem P).1 hP).2.1⟩)
  have hgP : ∀ P ∈ T, g P = (Ideal.absNorm P : ℂ) ^ (-s) := by
    intro P hP
    simp only [g, T12B.gs]
    rw [trivChar_apply ⟨((hTmem P).1 hP).2.1, sup_top_eq _⟩, one_mul]
  have hind : (T12B.Cop T).indicator g = T12B.gs (trivChar 𝔪) s := by
    funext I
    by_cases hI : I ∈ T12B.Cop T
    · rw [Set.indicator_of_mem hI]
      by_cases hb : I = ⊥
      · subst hb; exact (T12B.gs_bot _ s).trans (T12B.gs_bot _ s).symm
      have hcop : I ⊔ 𝔪 = ⊤ := by
        by_contra hc
        obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hc
        have hM0 : M ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ le_sup_right.trans hle))
        exact hI M ((hTmem M).2 ⟨hM.isPrime, hM0, le_sup_right.trans hle⟩) (le_sup_left.trans hle)
      simp only [g, T12B.gs]
      rw [trivChar_apply ⟨hb, sup_top_eq _⟩, trivChar_apply ⟨hb, hcop⟩]
    · rw [Set.indicator_of_notMem hI]
      simp only [T12B.Cop, Set.mem_ofPred_eq, not_forall, not_not] at hI
      obtain ⟨P, hP, hle⟩ := hI
      have hne : ¬ (I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤) := by
        rintro ⟨-, h⟩
        apply ((hTmem P).1 hP).1.ne_top
        rw [eq_top_iff, ← h]; exact sup_le hle ((hTmem P).1 hP).2.2
      simp only [T12B.gs, trivChar]
      rw [if_neg hne, zero_mul]
  rw [T12B.lseries_eq_tsum _ (trivChar_norm_le 𝔪) hs, ← hind, ← hsv,
    dedekindZeta_eq_LSeries_trivChar, T12B.lseries_eq_tsum _ (trivChar_norm_le _) hs,
    finprod_mem_eq_finite_toFinset_prod _ hfin, ← hT, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun P hP => by rw [hgP P hP]

theorem hasProd_zetaS {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : EP 𝔪 => (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      ((∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
        (1 - (Ideal.absNorm P : ℂ) ^ (-s))) * dedekindZeta F s) := by
  rw [← LSeries_trivChar h𝔪 hs]
  refine (euler1 (trivChar 𝔪) s (trivChar_norm_le 𝔪) hs).1.congr_fun fun P => ?_
  rw [trivChar_apply ⟨P.2.2.1, P.2.2.2⟩, one_mul]

theorem hasProd_inv_LSeries {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (hχ : ∀ I, ‖χ.toFun I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : EP 𝔪 => 1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))
      (χ.LSeries s)⁻¹ := by
  obtain ⟨h1, h2⟩ := euler1 χ s hχ hs
  have h3 := (show Tendsto (fun T : Finset (EP 𝔪) => ∏ b ∈ T,
      (1 - χ.toFun b.1 * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-s))⁻¹)
      (SummationFilter.unconditional _).filter (𝓝 (χ.LSeries s)) from h1).inv₀ h2
  refine h3.congr fun T => ?_
  rw [Finset.prod_inv_distrib, inv_inv]

end C3A

end ArtinPrimitiveRoots
end

section
/-! # C3P_Maj: the majorants and the Fubini swaps

`u t = (1 + t²)⁻¹`, `γ x = exp(−x²/2)`, and the three-variable majorant
`u t₁ · u t₂ · γ (t₁ + t₃)`; `e^{−(t₁+t₃)²} u t₃ ≤ 4 u t₁ γ(t₁+t₃)` moves the Gaussian's decay onto
the outer variable. -/

open MeasureTheory Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-! ### Integrability of the majorants -/

/-! ### Fubini -/

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3P_Bound: the principal-row integrand and its majorant

`Phi ξ w z = E(ξ,w,z) M(z) Ŵ(w) ζ(6z) ζ(w) G(ξ,w,z)` with `ζ(s) = R(s)/(s − 1)`, where
`E = X^{1/2−z} Z^{ξ+z−1} Y^{w−1} e^{(ξ+z−1)²}`; `Aw` and `Bz` are the numerators at the poles
`w = 1` and `z = 1/6`. -/

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

noncomputable section

/-! ### Elementary bounds -/

end

end C3P

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField Filter Asymptotics Finset

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

theorem T12C_map_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (k : ℕ) :
    χ.toFun (I ^ k) = χ.toFun I ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rwa [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
  | succ k ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- A finite-order Hecke character has absolute value `1` on nonzero ideals coprime to `𝔪`. -/
theorem T12C_norm_eq_one {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) : ‖χ.toFun I‖ = 1 := by
  classical
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    rw [sup_bot_eq] at hcop
    subst hcop
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rw [Ideal.span_singleton_one] at this
    rw [this, norm_one]
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hmk : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have hI0h : I ^ h ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hI)
  have hprin : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff hI0h).mp hmk
  obtain ⟨β, hβ⟩ := hprin.principal
  change I ^ h = Ideal.span {β} at hβ
  -- `hβ : I ^ h = span {β}`
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hβ
    exact pow_ne_zero h hI hβ
  have hcop' : Ideal.span {β} ⊔ 𝔪 = ⊤ := by rw [← hβ]; exact Ideal.pow_sup_eq_top hcop
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop'
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop'
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 r) ?_
    rw [← map_mul, mul_comm, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq]
    have : r * β - 1 = -z := by linear_combination hyz
    rw [this]
    exact 𝔪.neg_mem hz
  have hfin : Finite (𝓞 F ⧸ 𝔪) := Ring.HasFiniteQuotients.finiteQuotient h𝔪
  obtain ⟨m, hm, hum⟩ := (isOfFinOrder_of_finite hunit.unit).exists_pow_eq_one
  have hβm : Ideal.Quotient.mk 𝔪 (β ^ m) = 1 := by
    rw [map_pow]
    have := congrArg Units.val hum
    simpa using this
  have hχ : χ.toFun (Ideal.span {β ^ m}) = 1 := by
    refine χ.map_principal' _ (pow_ne_zero _ hβ0) ?_
    rw [← Ideal.Quotient.eq, map_one, hβm]
  rw [← Ideal.span_singleton_pow, ← hβ, ← pow_mul, T12C_map_pow] at hχ
  have hn := congrArg norm hχ
  rw [norm_pow, norm_one] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.mul_ne_zero hpos.ne' hm.ne')).mp hn

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

theorem T12C_pow_mod3 {M : Type*} [Monoid M] (z : M) (hz : z ^ 3 = 1) (m : ℕ) :
    z ^ m = z ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hz, one_pow, one_mul]

/-- A prime of norm divisible by `3` has norm at most `3^[F:ℚ]`. -/
theorem T12C_absNorm_le_of_three_dvd {F : Type*} [Field F] [NumberField F] (P : Ideal (𝓞 F))
    (hP0 : P ≠ ⊥) [P.IsMaximal] (h3 : 3 ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨f, hp, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at h3
  have h3p : 3 = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
  have h30 : ((3 : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [h3p]; exact ringChar.Nat.cast_ringChar
  have hmem : (3 : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    simpa using h30
  have hle : Ideal.span {(3 : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (3 : 𝓞 F) = 3 ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (3 : 𝓞 F) = algebraMap ℤ (𝓞 F) 3 by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow] at hdvd
  exact Nat.le_of_dvd (by positivity) hdvd

/-- `|J(ρ_P, ρ_P)|^6 / N P^3 = 1` for a prime `P` of norm `> 3^[F:ℚ]` of the cyclotomic field
`F = ℚ(μ_n)`, `3 ∣ n`. -/
theorem T12C_norm_jacobiPhaseSix (n : ℕ) (hn0 : 0 < n) (hn : 3 ∣ n) (F : Type*) [Field F]
    [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (P : Ideal (𝓞 F))
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) :
    ‖jacobiPhaseSix ι P‖ = 1 := by
  classical
  haveI : P.IsMaximal := hP.isMaximal hP0
  letI := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P with hQdef
  have hcard : Fintype.card (𝓞 F ⧸ P) = Q := by
    rw [hQdef, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hQ4 : 4 ≤ Q := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      have : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h3Q : ¬ 3 ∣ Q := fun h => by
    have := T12C_absNorm_le_of_three_dvd P hP0 h
    omega
  have hcop : Q.Coprime 3 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q))
  -- the cube root of unity
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 3)) 3 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  set ω₀ : 𝓞 F := hζ3.toInteger with hω₀
  have hω : IsPrimitiveRoot ω₀ 3 := hζ3.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P ω₀) 3 :=
    hω.idealQuotient_mk (by omega) hcop
  set ψ : ℂ := ι (ω₀ : F) with hψdef
  have hψ : IsPrimitiveRoot ψ 3 :=
    (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective
  set e := (Q - 1) / 3 with hedef
  have h3e : 3 * e = Q - 1 := by
    have h1 : Ideal.Quotient.mk P ω₀ ^ (Q - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
    have := (hωb.pow_eq_one_iff_dvd _).mp h1
    omega
  -- key lemma
  have KL : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∀ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i →
      cubicResidueChar ι P x = ψ ^ i := by
    intro x hx i hi
    have hex : ∃ ω : 𝓞 F, ω ^ 3 = 1 ∧ Ideal.Quotient.mk P ω = x ^ ((Ideal.absNorm P - 1) / 3) :=
      ⟨ω₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
        rw [map_pow, ← hi]⟩
    simp only [cubicResidueChar, if_neg hx, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    obtain ⟨j, hj, hjω⟩ := hω.eq_pow_of_pow_eq_one h1
    have hmk : Ideal.Quotient.mk P ω₀ ^ j = Ideal.Quotient.mk P ω₀ ^ (i % 3) := by
      rw [← map_pow, hjω, h2, ← T12C_pow_mod3 _ hωb.pow_eq_one]
      exact hi
    have hji : j = i % 3 := hωb.pow_inj hj (Nat.mod_lt _ (by norm_num)) hmk
    rw [← hjω, show ((ω₀ ^ j : 𝓞 F) : F) = (ω₀ : F) ^ j by norm_cast, map_pow, hji, ← T12C_pow_mod3 _ hψ.pow_eq_one]
  have EX : ∀ x : 𝓞 F ⧸ P, x ≠ 0 → ∃ i : ℕ, x ^ e = Ideal.Quotient.mk P ω₀ ^ i := by
    intro x hx
    have : (x ^ e) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, h3e, ← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, -, hi⟩ := hωb.eq_pow_of_pow_eq_one this
    exact ⟨i, hi.symm⟩
  have Z : cubicResidueChar ι P 0 = 0 := by simp [cubicResidueChar]
  let ρ : MulChar (𝓞 F ⧸ P) ℂ :=
    { toFun := cubicResidueChar ι P
      map_one' := by
        rw [KL 1 one_ne_zero 0 (by simp)]
        simp
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · simp [hx, Z]
        by_cases hy : y = 0
        · simp [hy, Z]
        obtain ⟨i, hi⟩ := EX x hx
        obtain ⟨j, hj⟩ := EX y hy
        rw [KL x hx i hi, KL y hy j hj, KL (x * y) (mul_ne_zero hx hy) (i + j)
          (by rw [mul_pow, hi, hj, pow_add]), pow_add]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (Ne.isUnit h)
        simp [this, Z] }
  have hρ : ∀ x, ρ x = cubicResidueChar ι P x := fun x => rfl
  -- a non-cube
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 F ⧸ P)ˣ)
  have hog : orderOf g = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card,
      hcard]
  obtain ⟨i, hi⟩ := EX (g : 𝓞 F ⧸ P) g.ne_zero
  have hi3 : ¬ 3 ∣ i := by
    intro h
    have h1 : (g : 𝓞 F ⧸ P) ^ e = 1 := by rw [hi, hωb.pow_eq_one_iff_dvd]; exact h
    have h2 : g ^ e = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hog] at this
    have hepos : 0 < e := by omega
    have := Nat.le_of_dvd hepos this
    omega
  have hρg : ρ g = ψ ^ i := KL _ g.ne_zero i hi
  have hρ1 : ρ ≠ 1 := by
    intro h
    have : ρ g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [hρg, hψ.pow_eq_one_iff_dvd] at this
    exact hi3 this
  have hρ2 : ρ * ρ ≠ 1 := by
    intro h
    have : (ρ * ρ) g = 1 := by rw [h]; exact MulChar.one_apply_coe g
    rw [MulChar.mul_apply, hρg, ← pow_add, hψ.pow_eq_one_iff_dvd] at this
    have : 3 ∣ 2 * i := by rwa [two_mul]
    exact hi3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this))
  have hch : ringChar ℂ ≠ ringChar (𝓞 F ⧸ P) := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite (𝓞 F ⧸ P)).symm
  have hJ := jacobiSum_mul_jacobiSum_inv hch hρ1 hρ1 hρ2
  rw [← MulChar.star_eq_inv] at hJ
  have hstar : jacobiSum (star ρ) (star ρ) = starRingEnd ℂ (jacobiSum ρ ρ) :=
    jacobiSum_ringHomComp ρ ρ (starRingEnd ℂ)
  rw [hstar, Complex.mul_conj', hcard] at hJ
  have hJn : ‖jacobiSum ρ ρ‖ ^ 2 = Q := by exact_mod_cast hJ
  have hcj : cubicJacobiSum ι P = jacobiSum ρ ρ := by
    rw [cubicJacobiSum, finsum_eq_sum_of_fintype]
    rfl
  rw [jacobiPhaseSix, hcj, norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast,
    show ‖jacobiSum ρ ρ‖ ^ 6 = (‖jacobiSum ρ ρ‖ ^ 2) ^ 3 by ring, hJn]
  have : (0 : ℝ) < (Q : ℝ) ^ 3 := by have : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
                                     positivity
  rw [← hQdef]
  field_simp

end ArtinPrimitiveRoots
end

section
/-! # C3P_Row: the principal-row correction `ℋ₁(ξ, w, z)` of Proposition 7.3

`rowLocalFactor Q e θ ξ w z` is `ℋ_{1,𝔭} = (1 − V)(1 − W)(1 − D₁)⁻¹ ℱ_{1,𝔭}` with `ℱ_{1,𝔭}` the
closed form (7.19) at `u = 1`: `Q = N𝔭`, `V = Q^{-6z}`, `W = Q^{-w}`, `D = e Q^{-ξ}` (`e = η(𝔭)`),
`E = θ Q^{4−6ξ} V` (`θ` in the place of `ϑ(𝔭)⁶`), multiplied out:
`[(1 − W) + W(1 − V) + (E((1 − Q⁻¹)(1 − W) + W(1 − V)(1 − W)) − D((1 − V)(1 − W) +
(Q − 1)WV(1 − W)))/(1 − E)] / (1 − D)`.
`rowCorrection` is the product over the exterior primes; on the box `Om` it is continuous,
separately holomorphic and bounded (`‖ℋ_𝔭 − 1‖ ≤ 50 Q^{-9/5}`), and at `(w, z) = (1, 1/6)` it is
`principalCorrection`. -/

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

/-- The local factor `ℋ_{1,𝔭}(ξ, w, z)` of Proposition 7.3 at `u = 1` ((7.19), multiplied out). -/
noncomputable def rowLocalFactor (Q : ℕ) (e θ ξ w z : ℂ) : ℂ :=
  let V := (Q : ℂ) ^ (-(6 * z))
  let W := (Q : ℂ) ^ (-w)
  let D := e * (Q : ℂ) ^ (-ξ)
  let E := θ * (Q : ℂ) ^ (4 - 6 * ξ) * V
  ((1 - W) + W * (1 - V) + (E * ((1 - (Q : ℂ)⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
    D * ((1 - V) * (1 - W) + ((Q : ℂ) - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)

/-- The principal-row correction `ℋ₁(ξ, w, z) = ∏_{𝔭 ∉ S} ℋ_{1,𝔭}`, with
`θ = conj(jacobiPhaseSix) · η⁶` in the place of `ϑ(𝔭)⁶`, as in `principalCorrection`. -/
noncomputable def rowCorrection {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (ι : F →+* ℂ) (χ : HeckeChar F 𝔪) (ξ w z : ℂ) : ℂ :=
  ∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
    rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
      (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) ξ w z

lemma rowLocal_alg (Q V W D E : ℂ) (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    ((1 - W) + W * (1 - V) + (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
      D * ((1 - V) * (1 - W) + (Q - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D) - 1 =
    (-(W * V) + (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))) / (1 - E)) / (1 - D) := by
  field_simp
  ring

/-- The local factor as a rational function of `Q, V, W, D, E`. -/
noncomputable def rlAlg (Q V W D E : ℂ) : ℂ :=
  ((1 - W) + W * (1 - V) + (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
    D * ((1 - V) * (1 - W) + (Q - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)

lemma rowLocalFactor_eq (Q : ℕ) (e θ ξ w z : ℂ) :
    rowLocalFactor Q e θ ξ w z = rlAlg (Q : ℂ) ((Q : ℂ) ^ (-(6 * z))) ((Q : ℂ) ^ (-w))
      (e * (Q : ℂ) ^ (-ξ)) (θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z))) := rfl

lemma rlAlg_bound (Q V W D E : ℂ) {q x : ℝ} (hq : 1 ≤ q) (hQn : ‖Q - 1‖ ≤ q)
    (hqi : ‖1 - Q⁻¹‖ ≤ 1) (hx0 : 0 ≤ x) (hxh : x ≤ 1 / 2) (hV : ‖V‖ ≤ x) (hW : ‖W‖ ≤ x)
    (hD : ‖D‖ ≤ q⁻¹) (hinv : q⁻¹ ≤ x) (hE : ‖E‖ ≤ x * x) :
    ‖rlAlg Q V W D E - 1‖ ≤ 50 * (x * x) ∧ 1 - D ≠ 0 ∧ 1 - E ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hDx : ‖D‖ ≤ x := hD.trans hinv
  have hx1 : x ≤ 1 := by linarith
  have hxx : x * x ≤ 1 / 2 := by nlinarith
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D; rw [norm_one] at this; linarith
  have h1E : 1 / 2 ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E; rw [norm_one] at this; linarith
  have hD0 : 1 - D ≠ 0 := fun h => by rw [h, norm_zero] at h1D; linarith
  have hE0 : 1 - E ≠ 0 := fun h => by rw [h, norm_zero] at h1E; linarith
  refine ⟨?_, hD0, hE0⟩
  have hV1 : ‖V‖ ≤ 1 := hV.trans hx1
  have hW1 : ‖W‖ ≤ 1 := hW.trans hx1
  have h1W : ‖1 - W‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h1V : ‖1 - V‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hQD : ‖(Q - 1) * D‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖Q - 1‖ * ‖D‖ ≤ q * q⁻¹ := mul_le_mul hQn hD (norm_nonneg _) hq0.le
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hA1 : ‖(1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)‖ ≤ 6 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖1 - Q⁻¹‖ * ‖1 - W‖ ≤ 1 * 2 := by gcongr
    have h2 : ‖W‖ * ‖1 - V‖ * ‖1 - W‖ ≤ 1 * 2 * 2 := by gcongr
    linarith
  have hN2 : ‖D * (V + W - V * W)‖ ≤ 3 * (x * x) := by
    rw [norm_mul]
    have h3 : ‖V + W - V * W‖ ≤ 3 * x := by
      have h4 : ‖V * W‖ ≤ x * 1 := by rw [norm_mul]; gcongr
      have := norm_sub_le (V + W) (V * W)
      have := norm_add_le V W
      linarith
    calc ‖D‖ * ‖V + W - V * W‖ ≤ x * (3 * x) := by gcongr
      _ = 3 * (x * x) := by ring
  have hN3 : ‖(Q - 1) * D * (W * V * (1 - W))‖ ≤ 2 * (x * x) := by
    rw [show ‖(Q - 1) * D * (W * V * (1 - W))‖ = ‖Q - 1‖ * ‖D‖ * (‖W‖ * ‖V‖ * ‖1 - W‖) by
      simp only [norm_mul]]
    rw [norm_mul] at hQD
    calc ‖Q - 1‖ * ‖D‖ * (‖W‖ * ‖V‖ * ‖1 - W‖) ≤ 1 * (x * x * 2) := by gcongr
      _ = 2 * (x * x) := by ring
  have hN4 : ‖D * E‖ ≤ x * x := by
    rw [norm_mul]
    calc ‖D‖ * ‖E‖ ≤ 1 * (x * x) := by gcongr; linarith
      _ = x * x := one_mul _
  have hN5 : ‖E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))‖ ≤ 6 * (x * x) := by
    rw [norm_mul]
    calc ‖E‖ * ‖(1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)‖ ≤ (x * x) * 6 := by gcongr
      _ = 6 * (x * x) := by ring
  have hnum : ‖D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))‖ ≤ 12 * (x * x) := by
    have a1 := norm_sub_le (D * (V + W - V * W)) ((Q - 1) * D * (W * V * (1 - W)))
    have a2 := norm_sub_le (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W))) (D * E)
    have a3 := norm_add_le (D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E)
      (E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W)))
    linarith
  have hquo : ‖(D * (V + W - V * W) - (Q - 1) * D * (W * V * (1 - W)) - D * E +
      E * ((1 - Q⁻¹) * (1 - W) + W * (1 - V) * (1 - W))) / (1 - E)‖ ≤ 24 * (x * x) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1E (by positivity : (0 : ℝ) ≤ 24 * (x * x))]
  have hWV : ‖-(W * V)‖ ≤ x * x := by rw [norm_neg, norm_mul]; gcongr
  have h25 := (norm_add_le _ _).trans (add_le_add hWV hquo)
  unfold rlAlg
  rw [rowLocal_alg Q V W D E hD0 hE0, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1D (by positivity : (0 : ℝ) ≤ 50 * (x * x))]

/-- The local bound on the box. -/
theorem rowLocal_bound (Q : ℕ) (hQ : 30 ≤ Q) (e θ ξ w z : ℂ) (he : ‖e‖ ≤ 1) (hθ : ‖θ‖ ≤ 1)
    (hξ : 1 < ξ.re) (hw : 9 / 10 < w.re) (hz : 3 / 20 < z.re) :
    ‖rowLocalFactor Q e θ ξ w z - 1‖ ≤ 50 * (Q : ℝ) ^ (-(9 / 5 : ℝ)) ∧
      1 - e * (Q : ℂ) ^ (-ξ) ≠ 0 ∧ 1 - θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z)) ≠ 0 := by
  have hq30 : (30 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hq0 : 0 < (Q : ℝ) := by linarith
  have hq1 : 1 ≤ (Q : ℝ) := by linarith
  have hnc : ∀ s : ℂ, ‖(Q : ℂ) ^ s‖ = (Q : ℝ) ^ s.re := fun s => by
    rw [show ((Q : ℕ) : ℂ) = (((Q : ℝ) : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hx0 : 0 ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := Real.rpow_nonneg hq0.le _
  have hx2 : (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) =
      (Q : ℝ) ^ (-(9 / 5 : ℝ)) := by
    rw [← Real.rpow_add hq0]; norm_num
  have hxh : (Q : ℝ) ^ (-(9 / 10 : ℝ)) ≤ 1 / 2 := by
    have h1 : (Q : ℝ) ^ (-(9 / 10 : ℝ)) ≤ (Q : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have h2 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow]
      have hs := Real.sq_sqrt hq0.le
      have hs0 := Real.sqrt_nonneg (Q : ℝ)
      have h2s : 2 ≤ Real.sqrt (Q : ℝ) := by nlinarith
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hinv : (Q : ℝ)⁻¹ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
  have hV : ‖(Q : ℂ) ^ (-(6 * z))‖ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [hnc]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
  have hW : ‖(Q : ℂ) ^ (-w)‖ ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [hnc]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
  have hD : ‖e * (Q : ℂ) ^ (-ξ)‖ ≤ (Q : ℝ)⁻¹ := by
    rw [norm_mul, hnc]
    have : (Q : ℝ) ^ (-ξ).re ≤ (Q : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]; apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
    calc ‖e‖ * (Q : ℝ) ^ (-ξ).re ≤ 1 * (Q : ℝ)⁻¹ := mul_le_mul he this (by positivity) zero_le_one
      _ = (Q : ℝ)⁻¹ := one_mul _
  have hE : ‖θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z))‖ ≤
      (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
    rw [norm_mul, norm_mul, hnc (4 - 6 * ξ)]
    have h1 : (Q : ℝ) ^ (4 - 6 * ξ).re ≤ (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hq1; simp; linarith
    calc ‖θ‖ * (Q : ℝ) ^ (4 - 6 * ξ).re * ‖(Q : ℂ) ^ (-(6 * z))‖ ≤
        1 * (Q : ℝ) ^ (-(9 / 10 : ℝ)) * (Q : ℝ) ^ (-(9 / 10 : ℝ)) := by gcongr
      _ = _ := by ring
  have hQn : ‖(Q : ℂ) - 1‖ ≤ (Q : ℝ) := by
    have : (Q : ℂ) - 1 = (((Q : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hqi : ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤ 1 := by
    have : (1 : ℂ) - (Q : ℂ)⁻¹ = ((1 - (Q : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : (Q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    have : 0 ≤ (Q : ℝ)⁻¹ := by positivity
    constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := rlAlg_bound (Q : ℂ) _ _ _ _ hq1 hQn hqi hx0 hxh hV hW hD hinv hE
  refine ⟨?_, h2, h3⟩
  rw [rowLocalFactor_eq, ← hx2]
  exact h1

end C3P

end ArtinPrimitiveRoots
end

section
/-! # C3A_Main: (7.12) at `u = 1` from the local multiplicativity of the frequency coefficients

`FreqCoeffLocal F ι` (the remaining cut) says: the coefficient
`a(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, u r⁶)` of `ℱ₁` (with `u` the principal frequency element)
is `1` at `(1,1,1,1)` and satisfies `a(P^{e₀}𝔠, P^l 𝔫, P^k 𝔰, P^m 𝔯) =
principalLocalCoeff(N P, η(P), ϑ(P)⁶; e₀, l, k, m) · a(𝔠, 𝔫, 𝔰, 𝔯)` for exterior primes `P` and
exterior `𝔠, 𝔫, 𝔰, 𝔯` prime to `P` (`𝔠` squarefree, `e₀ ≤ 1`). This is (7.16)–(7.17) of the paper.
From it, `chk_exists_cutoff_freqSeries_principalFreq_eq_of_freqCoeffLocal` proves the published cut
`exists_cutoff_freqSeries_principalFreq_eq` verbatim. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

/-- The coefficient `γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, u r⁶)` of `ℱ_u` (7.11). -/
noncomputable def freqCoeff {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) (u : SInt 𝔪) (𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)) : ℂ :=
  gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) * poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (u * g.gen 𝔯 ^ 6)

/-- **The remaining cut**: (7.16)–(7.17) at `u = 1`, as local multiplicativity of the coefficients
of the principal row. -/
def FreqCoeffLocal (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      freqCoeff g χ (freqElt g (principalFreq 𝔪)) ⊤ ⊤ ⊤ ⊤ = 1 ∧
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
        ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
          IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
          freqCoeff g χ (freqElt g (principalFreq 𝔪)) (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰)
              (P ^ m * 𝔯) =
            principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m *
              freqCoeff g χ (freqElt g (principalFreq 𝔪)) 𝔠 𝔫 𝔰 𝔯

/-! ### Elementary lemmas -/

lemma cpow_absNorm_pw (P I : Ideal (𝓞 F)) (a : ℕ) (s : ℂ) :
    ((Ideal.absNorm (P ^ a * I) : ℕ) : ℂ) ^ s =
      (((Ideal.absNorm P : ℕ) : ℂ) ^ s) ^ a * ((Ideal.absNorm I : ℕ) : ℂ) ^ s := by
  rw [map_mul, map_pow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  congr 1
  induction a with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

lemma exterior_pow_mul {𝔪 P I : Ideal (𝓞 F)} (hP : IsEP 𝔪 P) (hI : IsExterior 𝔪 I) (a : ℕ) :
    IsExterior 𝔪 (P ^ a * I) := by
  refine ⟨?_, ?_⟩
  · have hP0 : (P : Ideal (𝓞 F)) ≠ 0 := hP.2.1
    have hI0 : (I : Ideal (𝓞 F)) ≠ 0 := hI.1
    exact mul_ne_zero (pow_ne_zero a hP0) hI0
  · refine sup_mul_eq_top_iff.2 ⟨?_, hI.2⟩
    induction a with
    | zero => simp [Ideal.one_eq_top]
    | succ k ih => rw [pow_succ]; exact sup_mul_eq_top_iff.2 ⟨ih, hP.2.2⟩

lemma pw_mem_Om {𝔪 P : Ideal (𝓞 F)} (hP : IsEP 𝔪 P) (e : Exps) {y : Tup F} (hy : y ∈ Om 𝔪) :
    pw P e y ∈ Om 𝔪 :=
  ⟨exterior_pow_mul hP hy.1 _, exterior_pow_mul hP hy.2.1 _, exterior_pow_mul hP hy.2.2.1 _,
    exterior_pow_mul hP hy.2.2.2 _⟩

lemma squarefree_pow_mul {P c : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hc : Squarefree c)
    (hcP : ¬ c ≤ P) {a : ℕ} (ha : a ≤ 1) : Squarefree (P ^ a * c) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
  · simpa using hc
  · rw [pow_one]
    have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
    refine squarefree_mul_iff.2 ⟨hpr.irreducible.isRelPrime_iff_not_dvd.2 ?_, hpr.squarefree, hc⟩
    rwa [Ideal.dvd_iff_le]

lemma not_squarefree_pow_mul {P c : Ideal (𝓞 F)} (hP : P.IsPrime) {a : ℕ} (ha : 2 ≤ a) :
    ¬ Squarefree (P ^ a * c) := by
  intro h
  have hdvd : P * P ∣ P ^ a * c := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
    exact Dvd.intro (P ^ b * c) (by ring)
  have := h P hdvd
  rw [Ideal.isUnit_iff] at this
  exact hP.ne_top this

lemma coeff_eq_zero_of_two_le (Q : ℕ) (η θ : ℂ) {e₀ : ℕ} (h : 2 ≤ e₀) (l k m : ℕ) :
    principalLocalCoeff Q η θ e₀ l k m = 0 := by
  unfold principalLocalCoeff
  rw [if_neg (by omega), if_neg (by omega)]

lemma norm_coeff_le (Q : ℕ) (hQ : 1 ≤ Q) (η θ : ℂ) (hη : ‖η‖ ≤ 1) (hθ : ‖θ‖ ≤ 1)
    (e₀ l k m : ℕ) :
    ‖principalLocalCoeff Q η θ e₀ l k m‖ ≤
      Real.sqrt Q ^ e₀ * (Q : ℝ) ^ (3 * l) * (Q : ℝ) ^ k := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hs1 : (1 : ℝ) ≤ Real.sqrt Q := by rw [Real.one_le_sqrt]; exact hq
  have hθp : ∀ n : ℕ, ‖θ‖ ^ n ≤ 1 := fun n => pow_le_one₀ (norm_nonneg _) hθ
  have hQn : ‖(Q : ℂ)‖ = Q := Complex.norm_natCast Q
  have hsq : ‖((Real.sqrt Q : ℝ) : ℂ)‖ = Real.sqrt Q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hinv : ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤ 1 := by
    have : (1 : ℂ) - (Q : ℂ)⁻¹ = ((1 - (Q : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : (Q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
    have : 0 ≤ (Q : ℝ)⁻¹ := by positivity
    constructor <;> linarith
  have hQ1 : ‖(Q : ℂ) - 1‖ ≤ Q := by
    have : (Q : ℂ) - 1 = (((Q : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hp1 : ∀ n : ℕ, (1 : ℝ) ≤ (Q : ℝ) ^ n := fun n => one_le_pow₀ hq
  have hp1' : ∀ n : ℕ, (1 : ℝ) ≤ Real.sqrt Q ^ n := fun n => one_le_pow₀ hs1
  have hpos : ∀ n : ℕ, (0 : ℝ) ≤ (Q : ℝ) ^ n := fun n => by positivity
  unfold principalLocalCoeff
  split_ifs
  · rw [norm_one]
    nlinarith [hp1' e₀, hp1 (3 * l), hp1 k, mul_le_mul (hp1' e₀) (hp1 (3 * l)) zero_le_one
      (by positivity)]
  · rw [norm_zero]; positivity
  · -- k = 0
    rw [(‹k = 0 ∧ l / 2 ≤ m›).1, ‹e₀ = 0›, pow_zero, pow_zero, one_mul, mul_one, norm_mul, norm_mul, norm_pow, norm_pow, hQn]
    calc ‖θ‖ ^ (l / 2) * (Q : ℝ) ^ (3 * l) * ‖(1 : ℂ) - (Q : ℂ)⁻¹‖ ≤
        1 * (Q : ℝ) ^ (3 * l) * 1 := by gcongr; exact hθp _
      _ = _ := by ring
  · rw [(‹k = 1 ∧ m = l / 2›).1, ‹e₀ = 0›, pow_zero, one_mul, pow_one, norm_mul, norm_pow, norm_pow, hQn]
    calc ‖θ‖ ^ (l / 2) * (Q : ℝ) ^ (3 * l) ≤ 1 * (Q : ℝ) ^ (3 * l) := by
          gcongr; exact hθp _
      _ ≤ (Q : ℝ) ^ (3 * l) * Q := by nlinarith [hpos (3 * l)]
  · rw [norm_zero]; positivity
  · rw [norm_zero]; positivity
  · rw [(‹e₀ = 1 ∧ Even l›).1, (‹k = 0 ∧ m = l / 2›).1, pow_one, pow_zero, mul_one, norm_mul, norm_mul, norm_neg, norm_mul, norm_pow,
      norm_pow, hQn, hsq]
    calc ‖η‖ * Real.sqrt Q * ‖θ‖ ^ (l / 2) * (Q : ℝ) ^ (3 * l) ≤
        1 * Real.sqrt Q * 1 * (Q : ℝ) ^ (3 * l) := by gcongr; exact hθp _
      _ = _ := by ring
  · rw [(‹e₀ = 1 ∧ Even l›).1, (‹k = 1 ∧ l / 2 < m›).1, pow_one, pow_one, norm_mul, norm_mul, norm_mul, norm_neg, norm_mul, norm_pow,
      norm_pow, hQn, hsq]
    calc ‖η‖ * Real.sqrt Q * ‖θ‖ ^ (l / 2) * (Q : ℝ) ^ (3 * l) * ‖(Q : ℂ) - 1‖ ≤
        1 * Real.sqrt Q * 1 * (Q : ℝ) ^ (3 * l) * Q := by gcongr; exact hθp _
      _ = _ := by ring
  · rw [norm_zero]; positivity
  · rw [norm_zero]; positivity

end C3A

end ArtinPrimitiveRoots
end

section
/-! # C3A_Fac: the local factor on the initial lines

On `Re ξ > 3`, `Re w > 3`, `Re z > 1`, at a prime of norm `Q ≥ 2`:
`∑_e locTerm = (1 − Q^{-6z})⁻¹ (1 − Q^{-w})⁻¹ (1 − η Q^{-ξ}) ℋ_{1,𝔭}(ξ, w, z)` (`hasSum_locTerm`),
and the majorant `‖locTerm e‖ ≤ (Q^{-2})^{e₀+l+k+m}` (`norm_locTerm_le`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

lemma locSum_alg (q V W D E : ℂ) (hq : q ≠ 0) (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hE : 1 - E ≠ 0) :
    (1 - V)⁻¹ + W * (1 - W)⁻¹ + E * (1 - E)⁻¹ * ((1 - q⁻¹) * (1 - V)⁻¹) + E * (1 - E)⁻¹ * W +
        (-D) * (1 - E)⁻¹ + (-D) * (1 - E)⁻¹ * ((q - 1) * W * (V * (1 - V)⁻¹)) =
      (1 - V)⁻¹ * (1 - W)⁻¹ * (1 - D) * C3P.rlAlg q V W D E := by
  unfold C3P.rlAlg
  field_simp
  ring

lemma norm_natCast_cpow' {Q : ℕ} (hQ : 0 < Q) (s : ℂ) : ‖(Q : ℂ) ^ s‖ = (Q : ℝ) ^ s.re :=
  Complex.norm_natCast_cpow_of_pos hQ s

lemma rpow_le_neg_two {q x : ℝ} (hq : 1 ≤ q) (hx : x ≤ -2) : q ^ x ≤ q ^ (-2 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hq hx

section fac

variable (Q : ℕ) (e θ ξ w z : ℂ)

/-- The weights. -/
noncomputable abbrev wc : ℂ := (Q : ℂ) ^ (-(1 / 2 + ξ))
noncomputable abbrev wn : ℂ := (Q : ℂ) ^ (-(1 + 3 * ξ))
noncomputable abbrev ws : ℂ := (Q : ℂ) ^ (-w)
noncomputable abbrev wr : ℂ := (Q : ℂ) ^ (-(6 * z))

variable {Q e θ ξ w z}

lemma sqrt_mul_wc (hQ : 0 < Q) : (Real.sqrt Q : ℂ) * wc Q ξ = (Q : ℂ) ^ (-ξ) := by
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hs : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast; rfl
  rw [hs, wc, ← Complex.cpow_add _ _ hQ']
  congr 1; ring

lemma E_eq (hQ : 0 < Q) :
    θ * (Q : ℂ) ^ 6 * wn Q ξ ^ 2 * wr Q z = θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z)) := by
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have h6 : (Q : ℂ) ^ 6 = (Q : ℂ) ^ (6 : ℂ) := by
    rw [show (6 : ℂ) = ((6 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  rw [wn, wr, h6, pow_two, ← Complex.cpow_add _ _ hQ', mul_assoc θ, ← Complex.cpow_add _ _ hQ']
  congr 2; ring

theorem hasSum_locTerm (hQ : 2 ≤ Q) (he : ‖e‖ ≤ 1) (hθ : ‖θ‖ ≤ 1) (hξ : 3 < ξ.re)
    (hw : 3 < w.re) (hz : 1 < z.re) :
    HasSum (locTerm Q e θ (wc Q ξ) (wn Q ξ) (ws Q w) (wr Q z))
      ((1 - (Q : ℂ) ^ (-(6 * z)))⁻¹ * (1 - (Q : ℂ) ^ (-w))⁻¹ * (1 - e * (Q : ℂ) ^ (-ξ)) *
        C3P.rowLocalFactor Q e θ ξ w z) := by
  have hQ0 : 0 < Q := by omega
  have hq1 : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hlt : ∀ s : ℂ, s.re < 0 → ‖(Q : ℂ) ^ s‖ < 1 := fun s hs => by
    rw [norm_natCast_cpow' hQ0]; exact Real.rpow_lt_one_of_one_lt_of_neg hq1 hs
  have hV : ‖wr Q z‖ < 1 := hlt _ (by simp; linarith)
  have hW : ‖ws Q w‖ < 1 := hlt _ (by simp; linarith)
  have hD : ‖e * (Q : ℂ) ^ (-ξ)‖ < 1 := by
    rw [norm_mul]
    calc ‖e‖ * ‖(Q : ℂ) ^ (-ξ)‖ ≤ 1 * ‖(Q : ℂ) ^ (-ξ)‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hlt _ (by simp; linarith)
  have hE' : ‖θ * (Q : ℂ) ^ (4 - 6 * ξ) * (Q : ℂ) ^ (-(6 * z))‖ < 1 := by
    rw [mul_assoc, ← Complex.cpow_add _ _ hQ', norm_mul]
    calc ‖θ‖ * ‖(Q : ℂ) ^ (4 - 6 * ξ + -(6 * z))‖ ≤ 1 * ‖(Q : ℂ) ^ (4 - 6 * ξ + -(6 * z))‖ := by
          gcongr
      _ < 1 := by rw [one_mul]; exact hlt _ (by simp; linarith)
  have hE : ‖θ * (Q : ℂ) ^ 6 * wn Q ξ ^ 2 * wr Q z‖ < 1 := by rw [E_eq hQ0]; exact hE'
  have ne1 : ∀ x : ℂ, ‖x‖ < 1 → 1 - x ≠ 0 := fun x hx h => by
    rw [sub_eq_zero] at h; rw [← h, norm_one] at hx; exact lt_irrefl _ hx
  have h := hasSum_local Q e θ (wc Q ξ) (wn Q ξ) (ws Q w) (wr Q z) hV hW hE
  convert h using 1
  unfold locSum
  simp only
  rw [mul_assoc e, sqrt_mul_wc hQ0, E_eq hQ0, C3P.rowLocalFactor_eq]
  exact (locSum_alg _ _ _ _ _ hQ' (ne1 _ hV) (ne1 _ hW) (ne1 _ hD) (ne1 _ hE')).symm

theorem norm_locTerm_le (hQ : 1 ≤ Q) (he : ‖e‖ ≤ 1) (hθ : ‖θ‖ ≤ 1) (hξ : 3 < ξ.re)
    (hw : 3 < w.re) (hz : 1 < z.re) (x : Exps) :
    ‖locTerm Q e θ (wc Q ξ) (wn Q ξ) (ws Q w) (wr Q z) x‖ ≤
      ((Q : ℝ) ^ (-2 : ℝ)) ^ x.1 * (((Q : ℝ) ^ (-2 : ℝ)) ^ x.2.1 *
        (((Q : ℝ) ^ (-2 : ℝ)) ^ x.2.2.1 * ((Q : ℝ) ^ (-2 : ℝ)) ^ x.2.2.2)) := by
  obtain ⟨e₀, l, k, m⟩ := x
  have hQ0 : 0 < Q := by omega
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  set r := (Q : ℝ) ^ (-2 : ℝ)
  have hsq : Real.sqrt Q = (Q : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h3 : (Q : ℝ) ^ (3 : ℕ) = (Q : ℝ) ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]; norm_num
  have b0 : Real.sqrt Q * ‖wc Q ξ‖ ≤ r := by
    rw [norm_natCast_cpow' hQ0, hsq, ← Real.rpow_add hq0]
    exact rpow_le_neg_two hq1 (by simp; linarith)
  have b1 : (Q : ℝ) ^ (3 : ℕ) * ‖wn Q ξ‖ ≤ r := by
    rw [norm_natCast_cpow' hQ0, h3, ← Real.rpow_add hq0]
    exact rpow_le_neg_two hq1 (by simp; linarith)
  have b2 : (Q : ℝ) * ‖ws Q w‖ ≤ r := by
    rw [norm_natCast_cpow' hQ0]
    have : (Q : ℝ) * (Q : ℝ) ^ (-w).re = (Q : ℝ) ^ (1 + (-w).re) := by
      rw [Real.rpow_add hq0, Real.rpow_one]
    rw [this]
    exact rpow_le_neg_two hq1 (by simp; linarith)
  have b3 : ‖wr Q z‖ ≤ r := by
    rw [norm_natCast_cpow' hQ0]
    exact rpow_le_neg_two hq1 (by simp; linarith)
  have hc := norm_coeff_le Q hQ e θ he hθ e₀ l k m
  simp only [locTerm, norm_mul, norm_pow]
  calc ‖principalLocalCoeff Q e θ e₀ l k m‖ * ‖wc Q ξ‖ ^ e₀ * ‖wn Q ξ‖ ^ l * ‖ws Q w‖ ^ k *
        ‖wr Q z‖ ^ m ≤
      (Real.sqrt Q ^ e₀ * (Q : ℝ) ^ (3 * l) * (Q : ℝ) ^ k) * ‖wc Q ξ‖ ^ e₀ * ‖wn Q ξ‖ ^ l *
        ‖ws Q w‖ ^ k * ‖wr Q z‖ ^ m := by gcongr
    _ = (Real.sqrt Q * ‖wc Q ξ‖) ^ e₀ * ((Q : ℝ) ^ (3 : ℕ) * ‖wn Q ξ‖) ^ l *
        ((Q : ℝ) * ‖ws Q w‖) ^ k * ‖wr Q z‖ ^ m := by rw [pow_mul]; ring
    _ ≤ r ^ e₀ * r ^ l * r ^ k * r ^ m := by gcongr
    _ = _ := by ring

end fac

end C3A

end ArtinPrimitiveRoots
end

section
/-! # C3A_Final: `exists_cutoff_freqSeries_principalFreq_eq` from `FreqCoeffLocal`

The frequency series `ℱ₁` is the sum over 4-tuples of a function multiplicative in the sense of
`EulerHyp` (by the cut `FreqCoeffLocal`); `euler4` turns it into the product of the local sums,
which are `(1 − Q^{-6z})⁻¹ (1 − Q^{-w})⁻¹ (1 − η Q^{-ξ}) ℋ_{1,𝔭}` (`hasSum_locTerm`); the Euler
products of `ζ^S` and `L(·, η)⁻¹` (`C3A_Euler1`) and the convergence of `ℋ₁` (C3P's local bound)
identify the product. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

theorem chk_exists_cutoff_freqSeries_principalFreq_eq_of_freqCoeffLocal
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hcut : FreqCoeffLocal F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ξ w z : ℂ), 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z =
          (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-(6 * z)))) * dedekindZeta F (6 * z) *
            ((∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-w))) * dedekindZeta F w) *
            (∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
              let Q : ℕ := Ideal.absNorm P.1
              let V := (Q : ℂ) ^ (-(6 * z))
              let W := (Q : ℂ) ^ (-w)
              let D := χ.toFun P.1 * (Q : ℂ) ^ (-ξ)
              let E := starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6 *
                (Q : ℂ) ^ (4 - 6 * ξ) * V
              ((1 - W) + W * (1 - V) + (E * ((1 - (Q : ℂ)⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
                D * ((1 - V) * (1 - W) + ((Q : ℂ) - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)) /
            χ.LSeries ξ := by
  classical
  obtain ⟨N₁, hN₁⟩ := hcut
  have hn3 : 3 ∣ n := (by norm_num : 3 ∣ 12).trans hn
  set d := Module.finrank ℤ (𝓞 F) with hd
  refine ⟨max N₁ (3 ^ (d + 4)), fun 𝔪 h𝔪 hS χ g ξ w z hξ hw hz => ?_⟩
  have hS1 : SmallPrimesDvd N₁ 𝔪 := fun P hP hP0 hPN => hS P hP hP0 (hPN.trans (le_max_left _ _))
  obtain ⟨hone, hloc⟩ := hN₁ 𝔪 h𝔪 hS1 χ g
  -- exterior primes are large
  have hbig : ∀ P, IsEP 𝔪 P → 3 ^ (d + 4) < Ideal.absNorm P := by
    intro P hP
    by_contra h
    have hle := hS P hP.1 hP.2.1 ((not_lt.1 h).trans (le_max_right _ _))
    have h2 := hP.2.2
    rw [sup_eq_left.mpr hle] at h2
    exact hP.1.ne_top h2
  have h81 : 81 ≤ 3 ^ (d + 4) :=
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h30 : ∀ P, IsEP 𝔪 P → 30 ≤ Ideal.absNorm P := fun P hP => by
    have := hbig P hP; omega
  have hχ : ∀ I, ‖χ.toFun I‖ ≤ 1 := T12B.norm_le_one h𝔪 χ
  have hθ : ∀ P, IsEP 𝔪 P →
      ‖starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6‖ ≤ 1 := by
    intro P hP
    have hd3 : 3 ^ d < Ideal.absNorm P := by
      have := hbig P hP
      have : 3 ^ d ≤ 3 ^ (d + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [norm_mul, Complex.norm_conj, T12C_norm_jacobiPhaseSix n hn0 hn3 F ι P hP.1 hP.2.1 hd3,
      norm_pow, T12C_norm_eq_one χ P hP.2.1 hP.2.2]
    norm_num
  set u := freqElt g (principalFreq 𝔪) with hu
  -- the function on 4-tuples and its local factors
  set f : Tup F → ℂ := fun x => if x ∈ Om 𝔪 ∧ Squarefree x.1 then
      freqCoeff g χ u x.1 x.2.1 x.2.2.1 x.2.2.2 *
        ((Ideal.absNorm x.1 : ℕ) : ℂ) ^ (-(1 / 2 + ξ)) *
        ((Ideal.absNorm x.2.1 : ℕ) : ℂ) ^ (-(1 + 3 * ξ)) *
        ((Ideal.absNorm x.2.2.1 : ℕ) : ℂ) ^ (-w) * ((Ideal.absNorm x.2.2.2 : ℕ) : ℂ) ^ (-(6 * z))
    else 0 with hf
  set A : Ideal (𝓞 F) → Exps → ℂ := fun P => locTerm (Ideal.absNorm P) (χ.toFun P)
    (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) (wc (Ideal.absNorm P) ξ)
    (wn (Ideal.absNorm P) ξ) (ws (Ideal.absNorm P) w) (wr (Ideal.absNorm P) z) with hA
  -- (a) the frequency series as a sum over 4-tuples
  have hfs : χ.freqSeries g u ξ w z = ∑' x, f x := by
    unfold HeckeChar.freqSeries
    let emb : ({𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
        {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰} ×
        {𝔯 : Ideal (𝓞 F) // IsExterior 𝔪 𝔯}) → Tup F :=
      fun p => (p.1.1, p.2.1.1, p.2.2.1.1, p.2.2.2.1)
    have hinj : Function.Injective emb := by
      rintro ⟨⟨a1, _⟩, ⟨a2, _⟩, ⟨a3, _⟩, ⟨a4, _⟩⟩ ⟨⟨b1, _⟩, ⟨b2, _⟩, ⟨b3, _⟩, ⟨b4, _⟩⟩ h
      simp only [emb, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    have hsupp : Function.support f ⊆ Set.range emb := by
      intro x hx
      have hx' : f x ≠ 0 := hx
      by_cases hc : x ∈ Om 𝔪 ∧ Squarefree x.1
      · exact ⟨(⟨x.1, hc.1.1, hc.2⟩, ⟨x.2.1, hc.1.2.1⟩, ⟨x.2.2.1, hc.1.2.2.1⟩,
          ⟨x.2.2.2, hc.1.2.2.2⟩), rfl⟩
      · exact absurd (by simp only [hf]; rw [if_neg hc]) hx'
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun p => ?_
    have hc : emb p ∈ Om 𝔪 ∧ Squarefree (emb p).1 :=
      ⟨⟨p.1.2.1, p.2.1.2, p.2.2.1.2, p.2.2.2.2⟩, p.1.2.2⟩
    simp only [hf]
    rw [if_pos hc]
    rfl
  -- (b) multiplicativity
  have hmul : ∀ P, IsEP 𝔪 P → ∀ e y, y ∈ Om 𝔪 → y ∈ CopP P → f (pw P e y) = A P e * f y := by
    intro P hP e y hyO hyP
    obtain ⟨e₀, l, k, m⟩ := e
    obtain ⟨y1, y2, y3, y4⟩ := y
    by_cases hsq : Squarefree y1
    · by_cases he0 : e₀ ≤ 1
      · have hpwO := pw_mem_Om hP (e₀, l, k, m) hyO
        have hsq' := squarefree_pow_mul hP.1 hP.2.1 hsq hyP.1 he0
        simp only [hf, hA]
        rw [if_pos ⟨hpwO, hsq'⟩, if_pos ⟨hyO, hsq⟩]
        simp only [pw]
        rw [hloc P hP.1 ⟨hP.2.1, hP.2.2⟩ e₀ l k m he0 y1 y2 y3 y4 hyO.1 hsq hyO.2.1 hyO.2.2.1
          hyO.2.2.2 hyP.1 hyP.2.1 hyP.2.2.1 hyP.2.2.2, cpow_absNorm_pw, cpow_absNorm_pw,
          cpow_absNorm_pw, cpow_absNorm_pw]
        simp only [locTerm, wc, wn, ws, wr]
        ring
      · have h2 : 2 ≤ e₀ := by omega
        simp only [hf, hA]
        rw [if_neg (fun h => not_squarefree_pow_mul hP.1 h2 h.2), locTerm,
          coeff_eq_zero_of_two_le _ _ _ h2]
        ring
    · simp only [hf, hA, pw]
      rw [if_neg (fun h => hsq (Squarefree.of_mul_right h.2)), if_neg (fun h => hsq h.2), mul_zero]
  -- (c) majorant
  set rI : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-2 : ℝ) with hrI
  have hrI0 : ∀ I, 0 ≤ rI I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrImul : ∀ (P I : Ideal (𝓞 F)) (a : ℕ), rI (P ^ a * I) = rI P ^ a * rI I := by
    intro P I a
    simp only [hrI, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _),
      ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
  set B : Tup F → ℝ := fun x => rI x.1 * (rI x.2.1 * (rI x.2.2.1 * rI x.2.2.2)) with hB
  set β : Ideal (𝓞 F) → Exps → ℝ := fun P e =>
    rI P ^ e.1 * (rI P ^ e.2.1 * (rI P ^ e.2.2.1 * rI P ^ e.2.2.2)) with hβ
  have hBmul : ∀ P, IsEP 𝔪 P → ∀ e y, B (pw P e y) = β P e * B y := by
    intro P _ e y
    simp only [hB, hβ, pw, hrImul]
    ring
  have hAβ : ∀ P, IsEP 𝔪 P → ∀ e, ‖A P e‖ ≤ β P e := by
    intro P hP e
    have hQ1 : 1 ≤ Ideal.absNorm P := by have := h30 P hP; omega
    exact norm_locTerm_le hQ1 (hχ P) (hθ P hP) hξ hw hz e
  have hone4 : f one4 = 1 := by
    have hext : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩
    have hsqt : Squarefree (⊤ : Ideal (𝓞 F)) := by rw [← Ideal.one_eq_top]; exact squarefree_one
    simp only [hf, one4]
    rw [if_pos ⟨⟨hext, hext, hext, hext⟩, hsqt⟩, hone]
    simp [Ideal.absNorm_top]
  have hB1 : B one4 = 1 := by simp [hB, hrI, one4, Ideal.absNorm_top]
  have hbound : ∀ x, ‖f x‖ ≤ B x := by
    intro x
    by_cases hx : x ∈ Om 𝔪
    · exact norm_le_of_mul f A B β hmul hBmul hAβ (by rw [hone4, hB1, norm_one]) x hx
    · have : f x = 0 := by simp only [hf]; rw [if_neg (fun h => hx h.1)]
      rw [this, norm_zero]
      exact mul_nonneg (hrI0 _) (mul_nonneg (hrI0 _) (mul_nonneg (hrI0 _) (hrI0 _)))
  have hrIs : Summable rI := T12B.summable_absNorm_rpow (by norm_num : (1 : ℝ) < 2)
  have hB2 : Summable (fun q : Ideal (𝓞 F) × Ideal (𝓞 F) => rI q.1 * rI q.2) :=
    Summable.mul_of_nonneg (f := rI) (g := rI) hrIs hrIs hrI0 hrI0
  have hB3 : Summable (fun q : Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F) =>
      rI q.1 * (rI q.2.1 * rI q.2.2)) :=
    Summable.mul_of_nonneg (f := rI) (g := fun q : Ideal (𝓞 F) × Ideal (𝓞 F) => rI q.1 * rI q.2)
      hrIs hB2 hrI0 (fun _ => mul_nonneg (hrI0 _) (hrI0 _))
  have hBs : Summable B :=
    Summable.mul_of_nonneg (f := rI)
      (g := fun q : Ideal (𝓞 F) × Ideal (𝓞 F) × Ideal (𝓞 F) => rI q.1 * (rI q.2.1 * rI q.2.2))
      hrIs hB3 hrI0 (fun _ => mul_nonneg (hrI0 _) (mul_nonneg (hrI0 _) (hrI0 _)))
  have hfs' : Summable (fun x => ‖f x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hBs
  have hAs : ∀ P, IsEP 𝔪 P → Summable (fun e => ‖A P e‖) := by
    intro P hP
    have hr1 : rI P < 1 := by
      have hq : (1 : ℝ) < ((Ideal.absNorm P : ℕ) : ℝ) := by
        have := h30 P hP; exact_mod_cast (by omega : 1 < Ideal.absNorm P)
      exact Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
    have hg := summable_geometric_of_lt_one (hrI0 P) hr1
    have hp0 : ∀ k : ℕ, 0 ≤ rI P ^ k := fun k => pow_nonneg (hrI0 P) k
    have g2 : Summable (fun q : ℕ × ℕ => rI P ^ q.1 * rI P ^ q.2) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => rI P ^ k) (g := fun k : ℕ => rI P ^ k) hg hg hp0 hp0
    have g3 : Summable (fun q : ℕ × ℕ × ℕ => rI P ^ q.1 * (rI P ^ q.2.1 * rI P ^ q.2.2)) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => rI P ^ k)
        (g := fun q : ℕ × ℕ => rI P ^ q.1 * rI P ^ q.2) hg g2 hp0
        (fun _ => mul_nonneg (hp0 _) (hp0 _))
    have hβs : Summable (β P) :=
      Summable.mul_of_nonneg (f := fun k : ℕ => rI P ^ k)
        (g := fun q : ℕ × ℕ × ℕ => rI P ^ q.1 * (rI P ^ q.2.1 * rI P ^ q.2.2)) hg g3 hp0
        (fun _ => mul_nonneg (hp0 _) (mul_nonneg (hp0 _) (hp0 _)))
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hAβ P hP) hβs
  have hzero : ∀ x, x ∉ Om 𝔪 → f x = 0 := fun x hx => by
    simp only [hf]; rw [if_neg (fun h => hx h.1)]
  have hH : EulerHyp 𝔪 f A := ⟨hzero, hone4, hmul, hfs', hAs⟩
  -- (d) the Euler product of the series
  have hprod := (euler4 hH).1
  have hL : ∀ P : EP 𝔪, ∑' e, A P.1 e =
      (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-(6 * z)))⁻¹ *
        (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-w))⁻¹ *
        (1 - χ.toFun P.1 * ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-ξ)) *
        C3P.rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
          (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) ξ w z := by
    intro P
    have hQ2 : 2 ≤ Ideal.absNorm P.1 := by have := h30 P.1 P.2; omega
    exact (hasSum_locTerm hQ2 (hχ P.1) (hθ P.1 P.2) hξ hw hz).tsum_eq
  have hprod' := hprod.congr_fun fun P => (hL P).symm
  -- (e) the four Euler products
  have hz1 := hasProd_zetaS h𝔪 (s := 6 * z) (by simp; linarith)
  have hz2 := hasProd_zetaS h𝔪 (s := w) (by linarith)
  have hl := hasProd_inv_LSeries χ hχ (s := ξ) (by linarith)
  have hr : HasProd (fun P : EP 𝔪 => C3P.rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
      (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) ξ w z)
      (C3P.rowCorrection ι χ ξ w z) := by
    have hu : ∀ P : EP 𝔪, ‖C3P.rowLocalFactor (Ideal.absNorm P.1) (χ.toFun P.1)
        (starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6) ξ w z - 1‖ ≤
        50 * ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-(9 / 5 : ℝ)) := fun P =>
      (C3P.rowLocal_bound _ (h30 P.1 P.2) _ _ ξ w z (hχ P.1) (hθ P.1 P.2) (by linarith)
        (by linarith) (by linarith)).1
    have hs : Summable (fun P : EP 𝔪 => 50 * ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-(9 / 5 : ℝ))) :=
      ((T12B.summable_absNorm_rpow (F := F) (by norm_num : (1 : ℝ) < 9 / 5)).comp_injective
        Subtype.val_injective).mul_left 50
    have hm := Complex.multipliable_one_add_of_summable (Summable.of_norm_bounded hs hu)
    simp only [add_sub_cancel] at hm
    exact hm.hasProd
  have hall := ((hz1.mul hz2).mul hl).mul hr
  have heq := hprod'.unique hall
  rw [hfs, heq]
  show _ = _ * _ * C3P.rowCorrection ι χ ξ w z / _
  rw [div_eq_mul_inv]
  ring

end C3A

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (ξ w z : ℂ), 3 < ξ.re → 3 < w.re → 1 < z.re →
        χ.freqSeries g (freqElt g (principalFreq 𝔪)) ξ w z =
          (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-(6 * z)))) * dedekindZeta F (6 * z) *
            ((∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P},
              (1 - (Ideal.absNorm P : ℂ) ^ (-w))) * dedekindZeta F w) *
            (∏' P : {P : Ideal (𝓞 F) // P.IsPrime ∧ P ≠ ⊥ ∧ P ⊔ 𝔪 = ⊤},
              let Q : ℕ := Ideal.absNorm P.1
              let V := (Q : ℂ) ^ (-(6 * z))
              let W := (Q : ℂ) ^ (-w)
              let D := χ.toFun P.1 * (Q : ℂ) ^ (-ξ)
              let E := starRingEnd ℂ (jacobiPhaseSix ι P.1) * χ.toFun P.1 ^ 6 *
                (Q : ℂ) ^ (4 - 6 * ξ) * V
              ((1 - W) + W * (1 - V) + (E * ((1 - (Q : ℂ)⁻¹) * (1 - W) + W * (1 - V) * (1 - W)) -
                D * ((1 - V) * (1 - W) + ((Q : ℂ) - 1) * W * V * (1 - W))) / (1 - E)) / (1 - D)) /
            χ.LSeries ξ := by
  refine C3A.chk_exists_cutoff_freqSeries_principalFreq_eq_of_freqCoeffLocal n hn0 hn F ι ?_
  unfold C3A.FreqCoeffLocal
  exact exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul n hn0 hn F ι
end
