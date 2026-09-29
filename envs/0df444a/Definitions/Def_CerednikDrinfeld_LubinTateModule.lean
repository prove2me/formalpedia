-- Prove2me | Definitions.Def_CerednikDrinfeld_LubinTateModule
-- name    : CerednikDrinfeld_LubinTateModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/f318a136-124b-50cf-a64c-569f26dacd0f
-- title:
--   Lubin–Tate series, the formal group Σ, and its reduction
-- statement:
--   Fix a prime $p$. The first part works over $W(k)$ for a finite field $k$ of characteristic $p$, writes $q=\#k$ and puts $f(X_s)=pX_s+X_s^{q}$: `fvec` is the family $s\mapsto C(p)X_s+X_s^{q}$ indexed by a variable set $\tau$, the predicate `Comm` on $\varphi\in W(k)[[X_\tau]]$ asserts $p\varphi+\varphi^{q}=\varphi\bigl(f(X_s)\bigr)_{s}$ (substitution of `fvec` into $\varphi$), and `defect` is the difference of the two sides. The main result `existsUnique_series` states that for finite $\tau$ and any prescribed family $c\colon\tau\to W(k)$ there is exactly one $\varphi$ with zero constant term, $\operatorname{coeff}_{X_s}\varphi=c_s$ for all $s$, and satisfying that commutation relation. Uniqueness (`eq_of_comm`) compares coefficients degree by degree using that $p$ and $1-p^{n+1}$ are non-zero, the latter a unit in $W(k)$; existence builds successive approximations `approx`, correcting in each total degree by a term obtained from `defect`, which is divisible by $p$ coefficientwise because it vanishes modulo $p$, and `ltSeries` assembles the limit.
--
--   The second part specialises $k=\mathbb{F}_{p^{2}}$, so $q=p^{2}$, over the ring `Zp2 p`, here the Witt vectors of `GaloisField p 2`, and names the chosen solution `lt`. From it: `sigmaSeries` is the two-variable series with both linear coefficients $1$, packaged as a one-dimensional formal group law `sigma` (an [`MvFormalGroup`](../def/MvFormalGroup_BasicV2.html#L15) whose associativity and normalisation are structure fields), commutative; and `act₁ a` is the one-variable series with linear coefficient $a$, with $[1]=X$, $[0]=0$, $[ab]=[a]\circ[b]$, $[a+b]=\Sigma([a],[b])$ and $[p]=pX+X^{p^{2}}$. Coefficientwise Witt Frobenius fixes `sigmaSeries` and sends `act₁ a` to `act₁ (σa)`. Given a commutative ring $B$ and $j\colon$ `Zp2 p` $\to B$, `sigmaBar j` is the image formal group, `rho j` the ring homomorphism sending $a$ to the endomorphism with series $j([a])$; for $B$ of characteristic $p$, `phi j` is the endomorphism $X_0^{p}$, and $\varphi\rho(a)=\rho(\sigma a)\varphi$, $\varphi^{2}=\rho(p)$.
--
--   **Relation to Mathlib.** The multivariate formal-group structures used ([`MvFormalGroup`](../def/MvFormalGroup_BasicV2.html#L15), its homomorphisms and endomorphism ring) are the project's own, from the imported definition modules; Witt vectors, `GaloisField` and substitution for multivariate power series are Mathlib's.
--
--   **Where it is used.** These series and the pair $(\rho,\varphi)$ are the one-dimensional input for Drinfeld's special formal $\mathcal{O}_D$-modules, the objects behind the $p$-adic uniformisation of Shimura curves; within the project they serve the Čerednik–Drinfeld material supporting the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_LubinTateModule.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.LubinTateLemma

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [CharP k p]

theorem two_le_card : 2 ≤ Fintype.card k := Fintype.one_lt_card

theorem card_ne_zero : Fintype.card k ≠ 0 := by
  have := two_le_card (k := k); omega

theorem constantCoeff_natCast_p : WittVector.constantCoeff (p : WittVector p k) = 0 := by
  rw [WittVector.constantCoeff_apply, WittVector.coeff_p_zero]

theorem p_ne_zero' : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k

theorem isUnit_one_sub_pow (r : ℕ) : IsUnit (1 - (p : WittVector p k) ^ (r + 1)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_pow, constantCoeff_natCast_p,
    zero_pow (Nat.succ_ne_zero r), sub_zero]
  exact one_ne_zero

theorem one_sub_pow_ne_zero (r : ℕ) : (1 - (p : WittVector p k) ^ (r + 1)) ≠ 0 :=
  (isUnit_one_sub_pow r).ne_zero

theorem exists_eq_p_mul_of_coeff_zero (x : WittVector p k) (hx : x.coeff 0 = 0) :
    ∃ y : WittVector p k, x = (p : WittVector p k) * y := by
  have h1 : x = WittVector.verschiebung (x.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := x) (n := 1) (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact hx)
    simpa using this
  obtain ⟨y, hy⟩ := (WittVector.frobenius_bijective p k).2 (x.shift 1)
  refine ⟨y, ?_⟩
  rw [h1, ← hy, WittVector.verschiebung_frobenius, mul_comm]

variable (p k)

def fvec (τ : Type*) : τ → MvPowerSeries τ (WittVector p k) :=
  fun s => C (p : WittVector p k) * X s + X s ^ Fintype.card k

def Comm {τ : Type*} (φ : MvPowerSeries τ (WittVector p k)) : Prop :=
  C (p : WittVector p k) * φ + φ ^ Fintype.card k = subst (fvec p k τ) φ

def defect {τ : Type*} (θ : MvPowerSeries τ (WittVector p k)) : MvPowerSeries τ (WittVector p k) :=
  C (p : WittVector p k) * θ + θ ^ Fintype.card k - subst (fvec p k τ) θ

variable {p k}

section Family

variable {τ : Type*}

theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p k τ s) = 0 := by
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow (card_ne_zero (k := k)), add_zero]

theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p k τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

theorem coeff_single_X_pow_card [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) ((X s : MvPowerSeries τ (WittVector p k)) ^ Fintype.card k) = 0 := by
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d t) h
  simp only [Finsupp.single_eq_same] at this
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same] at this
    have := two_le_card (k := k)
    omega
  · rw [Finsupp.single_eq_of_ne hts] at this
    exact one_ne_zero this

theorem coeff_single_fvec [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) (fvec p k τ s) = if t = s then (p : WittVector p k) else 0 := by
  rw [fvec, map_add, coeff_C_mul, coeff_index_single_X, coeff_single_X_pow_card, add_zero]
  split_ifs <;> simp

theorem comm_X [Finite τ] (s : τ) : Comm p k (X s : MvPowerSeries τ (WittVector p k)) := by
  unfold Comm
  rw [subst_X hasSubst_fvec]
  rfl

theorem constantCoeff_C_mul_X (s : τ) :
    constantCoeff (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) = 0 := by
  rw [map_mul, constantCoeff_X, mul_zero]

theorem comm_subst {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ (WittVector p k)}
    (hφ : Comm p k φ) {a : σ → MvPowerSeries τ (WittVector p k)}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, Comm p k (a s)) :
    Comm p k (subst a φ) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  unfold Comm at *
  calc C (p : WittVector p k) * subst a φ + subst a φ ^ Fintype.card k
      = subst a (C (p : WittVector p k) * φ + φ ^ Fintype.card k) := by
        rw [subst_add hsa, subst_mul hsa, subst_pow hsa, subst_C]
    _ = subst a (subst (fvec p k σ) φ) := by rw [hφ]
    _ = subst (fun s => subst a (fvec p k σ s)) φ :=
        subst_comp_subst_apply hasSubst_fvec hsa φ
    _ = subst (fun s => subst (fvec p k τ) (a s)) φ := by
        congr 1
        funext s
        show subst a (C (p : WittVector p k) * X s + X s ^ Fintype.card k) = _
        rw [subst_add hsa, subst_mul hsa, subst_C, subst_pow hsa, subst_X hsa]
        exact ha s
    _ = subst (fvec p k τ) (subst a φ) := (subst_comp_subst_apply hsa hasSubst_fvec φ).symm

end Family

section Leading

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem finsuppProd_C_mul_X_pow (m : τ →₀ ℕ) :
    (m.prod fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = C ((p : WittVector p k) ^ m.degree) * monomial m 1 := by
  have h : (fun s e => (C (p : WittVector p k) * (X s : MvPowerSeries τ (WittVector p k))) ^ e)
      = fun s e => C ((p : WittVector p k) ^ e) * X s ^ e := by
    funext s e
    rw [mul_pow, map_pow]
  rw [h, Finsupp.prod_mul, ← monomial_one_eq, ← map_finsuppProd]
  congr 2
  rw [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

theorem coeff_finsuppProd_fvec_pow {d m : τ →₀ ℕ} (hdm : d.degree = m.degree) :
    coeff d (m.prod fun s e => (fvec p k τ s) ^ e)
      = if d = m then (p : WittVector p k) ^ m.degree else 0 := by
  have hcc : ∀ s, ∀ e : τ →₀ ℕ, e.degree < 2 →
      coeff e (fvec p k τ s) = coeff e (C (p : WittVector p k) * X s) := by
    intro s e he
    rw [fvec, map_add, add_eq_left, coeff_X_pow, if_neg]
    intro h
    subst h
    rw [Finsupp.degree_single] at he
    have := two_le_card (k := k)
    omega
  have key := MvFormalGroup.coeff_finsuppProd_pow_sub_congr (N := 2) (by norm_num)
    (c := fvec p k τ) (c' := fun s => C (p : WittVector p k) * X s)
    constantCoeff_fvec constantCoeff_C_mul_X hcc (m := m) (d := d) (by omega)
  rw [key, finsuppProd_C_mul_X_pow, coeff_C_mul, coeff_monomial]
  split_ifs <;> simp

theorem coeff_subst_fvec {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (hθ : ∀ e : τ →₀ ℕ, e.degree < n → coeff e θ = 0) {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (subst (fvec p k τ) θ) = (p : WittVector p k) ^ d.degree * coeff d θ := by
  rw [coeff_subst hasSubst_fvec, finsum_eq_single _ d]
  · rw [coeff_finsuppProd_fvec_pow rfl, if_pos rfl, smul_eq_mul, mul_comm]
  · intro m hm
    rcases lt_trichotomy m.degree d.degree with hlt | heq | hgt
    · rw [hθ m (by omega), zero_smul]
    · rw [coeff_finsuppProd_fvec_pow heq.symm, if_neg (Ne.symm hm), smul_zero]
    · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hgt,
        smul_zero]

end Leading

section Divisible

variable {τ : Type*}

include p in

theorem pow_card_eq_subst_X_pow (g : MvPowerSeries τ k) :
    g ^ Fintype.card k = subst (fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k) g := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card k p
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [hn, ← map_iterateFrobenius_expand p hp0 g n, iterateFrobenius_eq_pow,
    FiniteField.frobenius_pow hn, RingHom.one_def, MvPowerSeries.map_id, RingHom.id_apply]
  unfold MvPowerSeries.expand
  rw [substAlgHom_apply]

theorem map_defect_eq_zero [Finite τ] (θ : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k) (defect p k θ) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  rw [defect, map_sub, map_add, map_mul, map_pow, map_C, constantCoeff_natCast_p, map_zero,
    zero_mul, zero_add, map_subst hf, sub_eq_zero]
  have hfam : (fun s => MvPowerSeries.map (WittVector.constantCoeff : WittVector p k →+* k)
      (fvec p k τ s)) = fun s : τ => (X s : MvPowerSeries τ k) ^ Fintype.card k := by
    funext s
    simp only [fvec, map_add, map_mul, map_C, constantCoeff_natCast_p, map_zero, zero_mul,
      zero_add, map_pow, map_X]
  rw [hfam]
  exact pow_card_eq_subst_X_pow _

theorem exists_coeff_defect_eq_mul [Finite τ] (θ : MvPowerSeries τ (WittVector p k))
    (e : τ →₀ ℕ) : ∃ y : WittVector p k, coeff e (defect p k θ) = (p : WittVector p k) * y := by
  apply exists_eq_p_mul_of_coeff_zero
  rw [← WittVector.constantCoeff_apply, ← MvPowerSeries.coeff_map, map_defect_eq_zero, map_zero]

end Divisible

section Unique

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem eq_zero_or_single_of_degree_le_one {d : τ →₀ ℕ} (hd : d.degree ≤ 1) :
    d = 0 ∨ ∃ s, d = Finsupp.single s 1 := by
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · left
    exact (Finsupp.degree_eq_zero_iff d).mp (by omega)
  · right
    have hdeg : d.degree = 1 := le_antisymm hd h1
    have hmem : d ∈ {d' : τ →₀ ℕ | d'.degree = 1} := hdeg
    rw [← Finsupp.range_single_one] at hmem
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.symm⟩

theorem eq_of_comm {φ ψ : MvPowerSeries τ (WittVector p k)}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ)
    (hφ : Comm p k φ) (hψ : Comm p k ψ) : φ = ψ := by
  suffices key : ∀ n : ℕ, ∀ d : τ →₀ ℕ, d.degree ≤ n + 1 → coeff d φ = coeff d ψ from
    MvPowerSeries.ext fun d => key d.degree d (Nat.le_succ _)
  intro n
  induction n with
  | zero =>
    intro d hd
    rcases eq_zero_or_single_of_degree_le_one hd with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hφ0, hψ0]
    · exact h1 s
  | succ n IH =>
    intro d hd
    by_cases hlt : d.degree ≤ n + 1
    · exact IH d hlt
    have hdeg : d.degree = n + 2 := by omega
    have hf : HasSubst (fvec p k τ) := hasSubst_fvec
    have hδ : ∀ e : τ →₀ ℕ, e.degree < n + 2 → coeff e (φ - ψ) = 0 := by
      intro e he
      rw [map_sub, IH e (by omega), sub_self]
    have hpow : coeff d (φ ^ Fintype.card k) = coeff d (ψ ^ Fintype.card k) :=
      MvFormalGroup.coeff_pow_sub_congr (N := n + 2) (by omega) hφ0 hψ0
        (fun e he => IH e (by omega)) (by have := two_le_card (k := k); omega)
    have hsub : coeff d (subst (fvec p k τ) φ) - coeff d (subst (fvec p k τ) ψ)
        = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
      rw [← map_sub, ← subst_sub hf, coeff_subst_fvec hδ (le_of_eq hdeg), hdeg]
    have eφ := congrArg (coeff d) hφ
    have eψ := congrArg (coeff d) hψ
    simp only [map_add, coeff_C_mul] at eφ eψ
    have hc : (p : WittVector p k) * (1 - (p : WittVector p k) ^ (n + 1)) * coeff d (φ - ψ) = 0 := by
      have : (p : WittVector p k) * coeff d (φ - ψ)
          = (p : WittVector p k) ^ (n + 2) * coeff d (φ - ψ) := by
        rw [← hsub, ← eφ, ← eψ, hpow, map_sub]
        ring
      linear_combination this
    rcases mul_eq_zero.mp hc with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' p_ne_zero'
      · exact absurd h' (one_sub_pow_ne_zero n)
    · rwa [map_sub, sub_eq_zero] at h

end Unique

section Exists

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

open scoped Classical in

def pdiv (x : WittVector p k) : WittVector p k :=
  if h : ∃ y : WittVector p k, x = (p : WittVector p k) * y then h.choose else 0

theorem pdiv_spec {x : WittVector p k} (h : ∃ y : WittVector p k, x = (p : WittVector p k) * y) :
    x = (p : WittVector p k) * pdiv x := by
  rw [pdiv, dif_pos h]
  exact h.choose_spec

def corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) : MvPowerSeries τ (WittVector p k) :=
  fun d => if d.degree = n + 2 then
    -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
      * pdiv (coeff d (defect p k θ)) else 0

theorem coeff_corr (θ : MvPowerSeries τ (WittVector p k)) (n : ℕ) (d : τ →₀ ℕ) :
    coeff d (corr θ n) = if d.degree = n + 2 then
      -(((isUnit_one_sub_pow (p := p) (k := k) n).unit⁻¹ : (WittVector p k)ˣ) : WittVector p k)
        * pdiv (coeff d (defect p k θ)) else 0 := rfl

theorem coeff_corr_of_ne {θ : MvPowerSeries τ (WittVector p k)} {n : ℕ} {d : τ →₀ ℕ}
    (hd : d.degree ≠ n + 2) : coeff d (corr θ n) = 0 := by
  rw [coeff_corr, if_neg hd]

def approx (c : τ → WittVector p k) : ℕ → MvPowerSeries τ (WittVector p k)
  | 0 => ∑ s, C (c s) * X s
  | n + 1 => approx c n + corr (approx c n) n

theorem approx_succ (c : τ → WittVector p k) (n : ℕ) :
    approx c (n + 1) = approx c n + corr (approx c n) n := rfl

theorem coeff_approx_zero (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (approx c 0) = ∑ s, if d = Finsupp.single s 1 then c s else 0 := by
  show coeff d (∑ s, C (c s) * X s) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

theorem coeff_approx_zero_of_degree_ne_one (c : τ → WittVector p k) {d : τ →₀ ℕ}
    (hd : d.degree ≠ 1) : coeff d (approx c 0) = 0 := by
  rw [coeff_approx_zero]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [if_neg]
  rintro rfl
  exact hd (Finsupp.degree_single s 1)

theorem coeff_single_approx_zero (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (approx c 0) = c t := by
  rw [coeff_approx_zero, Finset.sum_eq_single t]
  · rw [if_pos rfl]
  · intro s _ hst
    rw [if_neg]
    intro h
    exact hst (Finsupp.single_left_injective one_ne_zero h).symm
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem coeff_approx_of_le (c : τ → WittVector p k) {n m : ℕ} (hnm : n ≤ m) {d : τ →₀ ℕ}
    (hd : d.degree ≤ n + 1) : coeff d (approx c m) = coeff d (approx c n) := by
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ m IH =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [approx_succ, map_add, coeff_corr_of_ne (by omega), add_zero]
      exact IH (by omega)
    · have hn : n = m + 1 := by omega
      subst hn
      rfl

theorem constantCoeff_approx (c : τ → WittVector p k) (n : ℕ) : constantCoeff (approx c n) = 0 := by
  have h0 : ((0 : τ →₀ ℕ)).degree = 0 := (Finsupp.degree_eq_zero_iff (0 : τ →₀ ℕ)).mpr rfl
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_approx_of_le c (Nat.zero_le n) (by omega),
    coeff_approx_zero_of_degree_ne_one c (by omega)]

theorem coeff_single_approx (c : τ → WittVector p k) (n : ℕ) (t : τ) :
    coeff (Finsupp.single t 1) (approx c n) = c t := by
  rw [coeff_approx_of_le c (Nat.zero_le n) (by rw [Finsupp.degree_single]),
    coeff_single_approx_zero]

theorem coeff_defect_approx (c : τ → WittVector p k) (n : ℕ) {e : τ →₀ ℕ}
    (he : e.degree ≤ n + 1) : coeff e (defect p k (approx c n)) = 0 := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  induction n generalizing e with
  | zero =>

    have hlin0 : ∀ e' : τ →₀ ℕ, e'.degree < 1 → coeff e' (approx c 0) = 0 :=
      fun e' he' => coeff_approx_zero_of_degree_ne_one c (by omega)
    rw [defect, map_sub, map_add, coeff_C_mul, coeff_subst_fvec hlin0 he,
      MvFormalGroup.coeff_pow_eq_zero_of_degree_lt (constantCoeff_approx c 0)
        (by have := two_le_card (k := k); omega), add_zero]
    rcases eq_zero_or_single_of_degree_le_one he with rfl | ⟨s, rfl⟩
    · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_approx, mul_zero, mul_zero, sub_self]
    · rw [Finsupp.degree_single, pow_one, sub_self]
  | succ n IH =>

    set θ := approx c n with hθ
    have hθ0 : constantCoeff θ = 0 := constantCoeff_approx c n
    have hκ : ∀ e' : τ →₀ ℕ, e'.degree < n + 2 → coeff e' (corr θ n) = 0 :=
      fun e' he' => coeff_corr_of_ne (by omega)
    have hκ0 : constantCoeff (corr θ n) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hκ 0 (by rw [map_zero]; omega)
    have hθ'0 : constantCoeff (θ + corr θ n) = 0 := by rw [map_add, hθ0, hκ0, add_zero]

    have hpow : coeff e ((θ + corr θ n) ^ Fintype.card k) = coeff e (θ ^ Fintype.card k) :=
      MvFormalGroup.coeff_pow_sub_congr (N := n + 2) (by omega) hθ'0 hθ0
        (fun e' he' => by rw [map_add, hκ e' he', add_zero])
        (by have := two_le_card (k := k); omega)
    have hexp : coeff e (defect p k (θ + corr θ n))
        = coeff e (defect p k θ) + ((p : WittVector p k) * coeff e (corr θ n)
            - coeff e (subst (fvec p k τ) (corr θ n))) := by
      simp only [defect, map_sub, map_add, coeff_C_mul, mul_add, subst_add hf, hpow]
      ring
    rw [approx_succ, hexp]
    rcases Nat.lt_or_ge e.degree (n + 2) with hlt | hge
    · rw [IH (by omega), coeff_subst_fvec hκ (le_of_lt hlt), hκ e hlt, mul_zero, mul_zero,
        sub_self, add_zero]
    · have hedeg : e.degree = n + 2 := by omega
      rw [coeff_subst_fvec hκ (le_of_eq hedeg), hedeg, coeff_corr, if_pos hedeg]
      set u : (WittVector p k)ˣ := (isUnit_one_sub_pow (p := p) (k := k) n).unit with hu
      have hu' : (u : WittVector p k) = 1 - (p : WittVector p k) ^ (n + 1) := rfl
      have hdiv := pdiv_spec (exists_coeff_defect_eq_mul θ e)
      set y := pdiv (coeff e (defect p k θ)) with hy
      rw [hdiv]
      have hinv : (u : WittVector p k) * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k) = 1 :=
        Units.mul_inv u
      linear_combination (-((p : WittVector p k) * y)) * hinv
        + ((p : WittVector p k) * y * ((u⁻¹ : (WittVector p k)ˣ) : WittVector p k)) * hu'

def ltSeries (c : τ → WittVector p k) : MvPowerSeries τ (WittVector p k) :=
  fun d => coeff d (approx c d.degree)

theorem coeff_ltSeries (c : τ → WittVector p k) (d : τ →₀ ℕ) :
    coeff d (ltSeries c) = coeff d (approx c d.degree) := rfl

theorem coeff_ltSeries_of_le (c : τ → WittVector p k) {n : ℕ} {d : τ →₀ ℕ} (hd : d.degree ≤ n + 1) :
    coeff d (ltSeries c) = coeff d (approx c n) := by
  rw [coeff_ltSeries]
  rcases Nat.lt_or_ge d.degree (n + 1) with h | h
  · rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
    · rw [h0]
      exact (coeff_approx_of_le c (Nat.zero_le n) (by omega)).symm
    · rw [coeff_approx_of_le c (show d.degree - 1 ≤ d.degree by omega) (by omega)]
      exact (coeff_approx_of_le c (show d.degree - 1 ≤ n by omega) (by omega)).symm
  · exact coeff_approx_of_le c (by omega) (by omega)

theorem constantCoeff_ltSeries (c : τ → WittVector p k) : constantCoeff (ltSeries c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ltSeries_of_le c (n := 0) (by rw [map_zero]; omega),
    coeff_zero_eq_constantCoeff_apply, constantCoeff_approx]

theorem coeff_single_ltSeries (c : τ → WittVector p k) (t : τ) :
    coeff (Finsupp.single t 1) (ltSeries c) = c t := by
  rw [coeff_ltSeries_of_le c (n := 0) (by rw [Finsupp.degree_single]), coeff_single_approx]

theorem coeff_defect_congr {θ θ' : MvPowerSeries τ (WittVector p k)} {n : ℕ}
    (h : ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e θ = coeff e θ') {d : τ →₀ ℕ} (hd : d.degree ≤ n) :
    coeff d (defect p k θ) = coeff d (defect p k θ') := by
  have hf : HasSubst (fvec p k τ) := hasSubst_fvec
  have hpow : coeff d (θ ^ Fintype.card k) = coeff d (θ' ^ Fintype.card k) :=
    MvFormalGroup.coeff_pow_congr h hd
  have hsub : coeff d (subst (fvec p k τ) θ) = coeff d (subst (fvec p k τ) θ') := by
    rw [← sub_eq_zero, ← map_sub, ← subst_sub hf, coeff_subst hf,
      finsum_eq_zero_of_forall_eq_zero]
    intro m
    rcases Nat.lt_or_ge d.degree m.degree with hlt | hge
    · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt constantCoeff_fvec hlt,
        smul_zero]
    · rw [map_sub, h m (by omega), sub_self, zero_smul]
  rw [defect, defect, map_sub, map_sub, map_add, map_add, coeff_C_mul, coeff_C_mul, h d hd, hpow,
    hsub]

theorem comm_ltSeries (c : τ → WittVector p k) : Comm p k (ltSeries c) := by
  unfold Comm
  rw [← sub_eq_zero]
  change defect p k (ltSeries c) = 0
  refine MvPowerSeries.ext fun d => ?_
  rw [map_zero, coeff_defect_congr (θ' := approx c d.degree) (n := d.degree)
    (fun e he => coeff_ltSeries_of_le c (by omega)) le_rfl]
  exact coeff_defect_approx c d.degree (Nat.le_succ _)

end Exists

end CerednikDrinfeld.LubinTateLemma

end

universe u v in
open CerednikDrinfeld.LubinTateLemma in
theorem CerednikDrinfeld.LubinTateLemma.existsUnique_series
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
    (τ : Type v) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ := by
  classical
  haveI : Fintype τ := Fintype.ofFinite τ
  refine ⟨ltSeries c, ⟨constantCoeff_ltSeries c, coeff_single_ltSeries c, comm_ltSeries c⟩, ?_⟩
  rintro ψ ⟨hψ0, hψ1, hψ⟩
  exact eq_of_comm hψ0 (constantCoeff_ltSeries c) (fun s => by rw [hψ1, coeff_single_ltSeries])
    hψ (comm_ltSeries c)

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.LubinTate

universe u v

variable {p : ℕ} [Fact p.Prime]

instance instFintypeGaloisFieldTwo : Fintype (GaloisField p 2) := Fintype.ofFinite _

theorem card_GF : Fintype.card (GaloisField p 2) = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 two_ne_zero]

theorem two_le_card : 2 ≤ Fintype.card (GaloisField p 2) := Fintype.one_lt_card

local notation "𝕆" => Zp2 p
local notation "𝔮" => Fintype.card (GaloisField p 2)

theorem frobenius_frobenius (a : 𝕆) : WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← sq,
    ← card_GF, FiniteField.pow_card]

theorem exists_pow_ne : ∃ ω : GaloisField p 2, ω ^ p ≠ ω := by
  classical
  by_contra h
  push Not at h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P : Polynomial (GaloisField p 2) := Polynomial.X ^ p - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1
  have hroots : ∀ ω : GaloisField p 2, ω ∈ P.roots := by
    intro ω
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h ω, sub_self]
  have hcard : Fintype.card (GaloisField p 2) ≤ p := by
    calc Fintype.card (GaloisField p 2) = (Finset.univ : Finset (GaloisField p 2)).card :=
          Finset.card_univ.symm
      _ ≤ P.roots.toFinset.card :=
          Finset.card_le_card fun ω _ => Multiset.mem_toFinset.mpr (hroots ω)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hdeg
  rw [card_GF, sq] at hcard
  have : p * p ≤ p * 1 := by simpa using hcard
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem exists_isUnit_frobenius_sub : ∃ a : 𝕆, IsUnit (WittVector.frobenius a - a) := by
  obtain ⟨ω, hω⟩ := exists_pow_ne (p := p)
  refine ⟨WittVector.teichmuller p ω, WittVector.isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr hω

variable (p)

def fvec (τ : Type*) : τ → MvPowerSeries τ 𝕆 :=
  fun s => C (p : 𝕆) * X s + X s ^ 𝔮

def Comm {τ : Type*} (φ : MvPowerSeries τ 𝕆) : Prop :=
  C (p : 𝕆) * φ + φ ^ 𝔮 = subst (fvec p τ) φ

theorem lt_existsUnique (τ : Type*) [Finite τ] (c : τ → 𝕆) :
    ∃! φ : MvPowerSeries τ 𝕆, constantCoeff φ = 0 ∧
      (∀ s, coeff (Finsupp.single s 1) φ = c s) ∧ Comm p φ :=
  CerednikDrinfeld.LubinTateLemma.existsUnique_series p (GaloisField p 2) τ c

def lt (τ : Type*) [Finite τ] (c : τ → 𝕆) : MvPowerSeries τ 𝕆 :=
  (lt_existsUnique p τ c).exists.choose

variable {p}

section LT

variable {τ : Type*}

theorem lt_spec [Finite τ] (c : τ → 𝕆) :
    constantCoeff (lt p τ c) = 0 ∧ (∀ s, coeff (Finsupp.single s 1) (lt p τ c) = c s) ∧
      Comm p (lt p τ c) :=
  (lt_existsUnique p τ c).exists.choose_spec

theorem constantCoeff_lt [Finite τ] (c : τ → 𝕆) : constantCoeff (lt p τ c) = 0 := (lt_spec c).1

theorem coeff_single_lt [Finite τ] (c : τ → 𝕆) (s : τ) :
    coeff (Finsupp.single s 1) (lt p τ c) = c s := (lt_spec c).2.1 s

theorem comm_lt [Finite τ] (c : τ → 𝕆) : Comm p (lt p τ c) := (lt_spec c).2.2

theorem eq_of_comm [Finite τ] {φ ψ : MvPowerSeries τ 𝕆}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0) (hφ : Comm p φ) (hψ : Comm p ψ)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ) : φ = ψ :=
  (lt_existsUnique p τ fun s => coeff (Finsupp.single s 1) ψ).unique ⟨hφ0, h1, hφ⟩
    ⟨hψ0, fun _ => rfl, hψ⟩

theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p τ s) = 0 := by
  have h0 : 𝔮 ≠ 0 := by have := two_le_card (p := p); omega
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow h0, add_zero]

theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

theorem coeff_single_X_pow_card [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) ((X s : MvPowerSeries τ 𝕆) ^ 𝔮) = 0 := by
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d t) h
  simp only [Finsupp.single_eq_same] at this
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same] at this
    have := two_le_card (p := p)
    omega
  · rw [Finsupp.single_eq_of_ne hts] at this
    exact one_ne_zero this

theorem coeff_single_fvec [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) (fvec p τ s) = if t = s then (p : 𝕆) else 0 := by
  rw [fvec, map_add, coeff_C_mul, coeff_index_single_X, coeff_single_X_pow_card, add_zero]
  split_ifs <;> simp

theorem comm_X [Finite τ] (s : τ) : Comm p (X s : MvPowerSeries τ 𝕆) := by
  unfold Comm
  rw [subst_X hasSubst_fvec]
  rfl

theorem comm_fvec [Finite τ] (s : τ) : Comm p (fvec p τ s) := by
  have hf : HasSubst (fvec p τ) := hasSubst_fvec
  unfold Comm
  conv_rhs => rw [fvec]
  rw [subst_add hf, subst_mul hf, subst_C, subst_pow hf, subst_X hf]

theorem comm_subst {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) {a : σ → MvPowerSeries τ 𝕆}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, Comm p (a s)) :
    Comm p (subst a φ) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  unfold Comm at *
  calc C (p : 𝕆) * subst a φ + subst a φ ^ 𝔮
      = subst a (C (p : 𝕆) * φ + φ ^ 𝔮) := by
        rw [subst_add hsa, subst_mul hsa, subst_pow hsa, subst_C]
    _ = subst a (subst (fvec p σ) φ) := by rw [hφ]
    _ = subst (fun s => subst a (fvec p σ s)) φ :=
        subst_comp_subst_apply hasSubst_fvec hsa φ
    _ = subst (fun s => subst (fvec p τ) (a s)) φ := by
        congr 1
        funext s
        show subst a (C (p : 𝕆) * X s + X s ^ 𝔮) = _
        rw [subst_add hsa, subst_mul hsa, subst_C, subst_pow hsa, subst_X hsa]
        exact ha s
    _ = subst (fvec p τ) (subst a φ) := (subst_comp_subst_apply hsa hasSubst_fvec φ).symm

theorem comm_subst_X {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) (e : σ → τ) :
    Comm p (subst (fun s => (X (e s) : MvPowerSeries τ 𝕆)) φ) :=
  comm_subst hφ (fun _ => constantCoeff_X _) fun _ => comm_X _

theorem constantCoeff_subst_of {σ : Type*} [Finite σ] {φ : MvPowerSeries σ 𝕆}
    (hφ : constantCoeff φ = 0) {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) :
    constantCoeff (subst a φ) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha0) ha0 hφ

theorem coeff_single_subst_lt {σ : Type*} [Fintype σ] [Fintype τ] (c : σ → 𝕆)
    {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (lt p σ c)) = ∑ s, c s * coeff (Finsupp.single t 1) (a s) := by
  rw [MvFormalGroup.coeff_single_subst ha0]
  simp only [coeff_single_lt]

end LT

section FrobeniusInvariance

variable {τ : Type*}

local notation "σ" => (WittVector.frobenius : Zp2 p →+* Zp2 p)

theorem map_frobenius_fvec (s : τ) : MvPowerSeries.map σ (fvec p τ s) = fvec p τ s := by
  rw [fvec, map_add, map_mul, map_C, map_natCast, map_X, map_pow, map_X]

theorem comm_map_frobenius [Finite τ] {φ : MvPowerSeries τ 𝕆} (hφ : Comm p φ) :
    Comm p (MvPowerSeries.map σ φ) := by
  unfold Comm at *
  have h := congrArg (MvPowerSeries.map σ) hφ
  rw [map_add, map_mul, map_C, map_natCast, map_pow, map_subst hasSubst_fvec] at h
  rw [h]
  congr 1
  funext s
  exact map_frobenius_fvec s

theorem map_frobenius_lt [Finite τ] (c : τ → 𝕆) :
    MvPowerSeries.map σ (lt p τ c) = lt p τ fun s => σ (c s) := by
  classical
  refine eq_of_comm ?_ (constantCoeff_lt _) (comm_map_frobenius (comm_lt c)) (comm_lt _) fun s => ?_
  · rw [constantCoeff_map, constantCoeff_lt, map_zero]
  · rw [coeff_map, coeff_single_lt, coeff_single_lt]

end FrobeniusInvariance

section Sigma

variable (p)

def sigmaSeries : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆 := lt p (Fin 1 ⊕ Fin 1) fun _ => 1

def act₁ (a : 𝕆) : MvPowerSeries (Fin 1) 𝕆 := lt p (Fin 1) fun _ => a

variable {p}

theorem constantCoeff_sigmaSeries : constantCoeff (sigmaSeries p) = 0 := constantCoeff_lt _

theorem comm_sigmaSeries : Comm p (sigmaSeries p) := comm_lt _

theorem coeff_single_sigmaSeries (v : Fin 1 ⊕ Fin 1) :
    coeff (Finsupp.single v 1) (sigmaSeries p) = 1 := by
  rw [sigmaSeries, coeff_single_lt]

theorem coeff_single_subst_sigmaSeries {τ : Type*} [Fintype τ]
    {a : Fin 1 ⊕ Fin 1 → MvPowerSeries τ 𝕆} (ha0 : ∀ v, constantCoeff (a v) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (sigmaSeries p))
      = coeff (Finsupp.single t 1) (a (Sum.inl 0)) + coeff (Finsupp.single t 1) (a (Sum.inr 0)) := by
  rw [sigmaSeries, coeff_single_subst_lt _ ha0, Fintype.sum_sum_type]
  simp only [one_mul, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]

theorem constantCoeff_act₁ (a : 𝕆) : constantCoeff (act₁ p a) = 0 := constantCoeff_lt _

theorem comm_act₁ (a : 𝕆) : Comm p (act₁ p a) := comm_lt _

theorem coeff_single_act₁ (a : 𝕆) (s : Fin 1) : coeff (Finsupp.single s 1) (act₁ p a) = a := by
  rw [act₁, coeff_single_lt]

theorem coeff_single_subst_act₁ {τ : Type*} [Fintype τ] (a : 𝕆)
    {b : Fin 1 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (act₁ p a)) = a * coeff (Finsupp.single t 1) (b 0) := by
  rw [act₁, coeff_single_subst_lt _ hb0]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]

theorem hasSubst_fin1 {τ : Type*} {x : MvPowerSeries τ 𝕆} (hx : constantCoeff x = 0) :
    HasSubst (fun _ : Fin 1 => x) :=
  hasSubst_of_constantCoeff_zero fun _ => hx

variable (p) in

def sigma : MvFormalGroup 1 𝕆 where
  toPowerSeries := fun _ => sigmaSeries p
  constantCoeff_eq_zero := fun _ => constantCoeff_sigmaSeries
  coeff_single_inl i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  coeff_single_inr i j := by
    rw [coeff_single_sigmaSeries, if_pos (Subsingleton.elim i j)]
  assoc i := by
    classical
    have hB : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hC : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hBv : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) = fun s => X (Sum.elim (fun l => Sum.inl l)
          (fun l => Sum.inr (Sum.inl l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hCv : (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) = fun s => X (Sum.elim (fun l => Sum.inr (Sum.inl l))
          (fun l => Sum.inr (Sum.inr l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hA : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun _ : Fin 1 => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
          fun l => X (Sum.inr (Sum.inl l))) (sigmaSeries p))
        fun j => X (Sum.inr (Sum.inr j))) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_subst_of constantCoeff_sigmaSeries hB
      · exact constantCoeff_X _
    have hA' : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
        fun _ : Fin 1 => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) 𝕆))
          fun l => X (Sum.inr (Sum.inr l))) (sigmaSeries p)) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_of constantCoeff_sigmaSeries hC
    refine eq_of_comm (constantCoeff_subst_of constantCoeff_sigmaSeries hA)
      (constantCoeff_subst_of constantCoeff_sigmaSeries hA') ?_ ?_ ?_
    · refine comm_subst comm_sigmaSeries hA ?_
      rintro (j | j)
      · show Comm p (subst _ (sigmaSeries p))
        rw [hBv]
        exact comm_subst_X comm_sigmaSeries _
      · exact comm_X _
    · refine comm_subst comm_sigmaSeries hA' ?_
      rintro (j | j)
      · exact comm_X _
      · show Comm p (subst _ (sigmaSeries p))
        rw [hCv]
        exact comm_subst_X comm_sigmaSeries _
    · intro t
      rw [coeff_single_subst_sigmaSeries hA, coeff_single_subst_sigmaSeries hA']
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [coeff_single_subst_sigmaSeries hB, coeff_single_subst_sigmaSeries hC]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact add_assoc _ _ _

@[simp] theorem sigma_toPowerSeries (i : Fin 1) : (sigma p).toPowerSeries i = sigmaSeries p := rfl

instance sigma_isComm : (sigma p).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (sigmaSeries p) = sigmaSeries p
    refine eq_of_comm (constantCoeff_subst_of constantCoeff_sigmaSeries hS)
      constantCoeff_sigmaSeries ?_ comm_sigmaSeries ?_
    · rw [hSv]
      exact comm_subst_X comm_sigmaSeries _
    · intro t
      rw [coeff_single_subst_sigmaSeries hS, coeff_single_sigmaSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      rcases t with l | l <;> rw [Fin.fin_one_eq_zero l] <;> simp

theorem constantCoeff_homFamily₁ {φ : MvPowerSeries (Fin 1) 𝕆} (hφ : constantCoeff φ = 0) :
    ∀ s : Fin 1 ⊕ Fin 1, constantCoeff ((Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) s) = 0 := by
  rintro (j | j) <;> exact constantCoeff_subst_of hφ (fun l => constantCoeff_X _)

theorem subst_sigma_eq_of_comm {φ : MvPowerSeries (Fin 1) 𝕆} (h0 : constantCoeff φ = 0)
    (hc : Comm p φ) :
    subst (sigma p).toPowerSeries φ =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        (sigmaSeries p) := by
  classical
  have hF : ∀ j : Fin 1, constantCoeff ((sigma p).toPowerSeries j) = 0 :=
    fun _ => constantCoeff_sigmaSeries
  have hA := constantCoeff_homFamily₁ h0
  refine eq_of_comm (constantCoeff_subst_of h0 hF)
    (constantCoeff_subst_of constantCoeff_sigmaSeries hA)
    (comm_subst hc hF fun _ => comm_sigmaSeries) (comm_subst comm_sigmaSeries hA ?_) ?_
  · rintro (j | j) <;> exact comm_subst_X hc _
  · intro t
    rw [coeff_single_subst_sigmaSeries hA, MvFormalGroup.coeff_single_subst hF]
    simp only [Sum.elim_inl, Sum.elim_inr, sigma_toPowerSeries, coeff_single_sigmaSeries,
      Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
    rw [MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _),
      MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _)]
    simp only [coeff_index_single_X, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, mul_ite, mul_one, mul_zero]
    rcases t with l | l <;> rw [Fin.fin_one_eq_zero l] <;> simp

theorem subst_sigma_act₁ (a : 𝕆) :
    subst (sigma p).toPowerSeries (act₁ p a) =
      subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) (act₁ p a))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) (act₁ p a))
        (sigmaSeries p) :=
  subst_sigma_eq_of_comm (constantCoeff_act₁ a) (comm_act₁ a)

theorem act₁_one : act₁ p 1 = X 0 := by
  classical
  refine eq_of_comm (constantCoeff_act₁ 1) (constantCoeff_X 0) (comm_act₁ 1) (comm_X 0) fun s => ?_
  rw [coeff_single_act₁, coeff_index_single_X, if_pos (Subsingleton.elim s 0)]

theorem act₁_zero : act₁ p 0 = 0 := by
  classical
  have h0 : Comm p (0 : MvPowerSeries (Fin 1) 𝕆) := by
    unfold Comm
    have hq : Fintype.card (GaloisField p 2) ≠ 0 := by have := two_le_card (p := p); omega
    rw [mul_zero, zero_pow hq, add_zero, ← coe_substAlgHom hasSubst_fvec, map_zero]
  refine eq_of_comm (constantCoeff_act₁ 0) (map_zero _) (comm_act₁ 0) h0 fun s => ?_
  rw [coeff_single_act₁, map_zero]

theorem act₁_mul (a b : 𝕆) : act₁ p (a * b) = subst (fun _ : Fin 1 => act₁ p b) (act₁ p a) := by
  classical
  refine eq_of_comm (constantCoeff_act₁ _)
    (constantCoeff_subst_of (constantCoeff_act₁ a) (fun _ => constantCoeff_act₁ b))
    (comm_act₁ _) (comm_subst (comm_act₁ a) (fun _ => constantCoeff_act₁ b) fun _ => comm_act₁ b)
    fun s => ?_
  rw [coeff_single_act₁, coeff_single_subst_act₁ a (fun _ => constantCoeff_act₁ b),
    coeff_single_act₁]

theorem act₁_add (a b : 𝕆) :
    act₁ p (a + b) = subst (Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b)
      (sigmaSeries p) := by
  classical
  have hab : ∀ s : Fin 1 ⊕ Fin 1, constantCoeff
      ((Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b) s) = 0 := by
    rintro (j | j) <;> exact constantCoeff_act₁ _
  refine eq_of_comm (constantCoeff_act₁ _) (constantCoeff_subst_of constantCoeff_sigmaSeries hab)
    (comm_act₁ _) (comm_subst comm_sigmaSeries hab ?_) fun s => ?_
  · rintro (j | j) <;> exact comm_act₁ _
  · rw [coeff_single_act₁, coeff_single_subst_sigmaSeries hab]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_act₁]

theorem act₁_natCast_p :
    act₁ p (p : 𝕆) = C (p : 𝕆) * X 0 + X 0 ^ Fintype.card (GaloisField p 2) := by
  classical
  refine eq_of_comm (constantCoeff_act₁ _) (constantCoeff_fvec 0) (comm_act₁ _) (comm_fvec 0)
    fun s => ?_
  show _ = coeff _ (fvec p (Fin 1) 0)
  rw [coeff_single_act₁, coeff_single_fvec, if_pos (Subsingleton.elim s 0)]

theorem map_frobenius_sigmaSeries :
    MvPowerSeries.map WittVector.frobenius (sigmaSeries p) = sigmaSeries p := by
  rw [sigmaSeries, map_frobenius_lt]
  simp only [map_one]

theorem map_frobenius_act₁ (a : 𝕆) :
    MvPowerSeries.map WittVector.frobenius (act₁ p a) = act₁ p (WittVector.frobenius a) := by
  rw [act₁, map_frobenius_lt]
  rfl

end Sigma

section Reduction

instance instIsCommMap {g : ℕ} {R S : Type*} [CommRing R] [CommRing S] (F : MvFormalGroup g R)
    [F.IsComm] (f : R →+* S) : (F.map f).IsComm := by
  constructor
  intro i
  have key := congrArg (MvPowerSeries.map f) (MvFormalGroup.IsComm.comm (F := F) i)
  have hS : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j) <;> exact constantCoeff_X _
  rw [map_subst hS] at key
  have hfam : (fun s => MvPowerSeries.map f (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun j => X (Sum.inl j)) s))
      = Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S))
        fun j => X (Sum.inl j) := by
    funext s
    rcases s with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

variable {B : Type u} [CommRing B]

theorem map_homIdentity₁ (f : 𝕆 →+* B) {F : Fin 1 → MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆}
    (hF : ∀ i, constantCoeff (F i) = 0) {G : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆}
    {φ : MvPowerSeries (Fin 1) 𝕆} (hφ : constantCoeff φ = 0)
    (h : subst F φ = subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) G) :
    subst (fun i => MvPowerSeries.map f (F i)) (MvPowerSeries.map f φ) = subst (Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ)) (MvPowerSeries.map f G) := by
  have hXl : ∀ l : Fin 1, constantCoeff
      ((X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) = 0 := fun l => constantCoeff_X _
  have hXr : ∀ l : Fin 1, constantCoeff
      ((X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) = 0 := fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXl) hXl hφ
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXr) hXr hφ
  have key := congrArg (MvPowerSeries.map f) h
  rw [map_subst (hasSubst_of_constantCoeff_zero hF), map_subst hA] at key
  have hAmap : (fun s => MvPowerSeries.map f (Sum.elim
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ)
      (fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) 𝕆)) φ) s))
      = Sum.elim
        (fun _ : Fin 1 => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ))
        fun _ : Fin 1 => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 1 ⊕ Fin 1) B))
          (MvPowerSeries.map f φ) := by
    funext s
    rcases s with j | j
    · show MvPowerSeries.map f (subst _ φ) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXl)]
      simp only [MvPowerSeries.map_X, Sum.elim_inl]
    · show MvPowerSeries.map f (subst _ φ) = _
      rw [map_subst (hasSubst_of_constantCoeff_zero hXr)]
      simp only [MvPowerSeries.map_X, Sum.elim_inr]
  rw [hAmap] at key
  exact key

variable (j : Zp2 p →+* B)

def sigmaBar : MvFormalGroup 1 B := (sigma p).map j

@[simp] theorem sigmaBar_toPowerSeries (i : Fin 1) :
    (sigmaBar j).toPowerSeries i = MvPowerSeries.map j (sigmaSeries p) := rfl

instance sigmaBar_isComm : (sigmaBar j).IsComm := instIsCommMap _ _

def rhoEnd (a : 𝕆) : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => MvPowerSeries.map j (act₁ p a)
  constantCoeff_eq_zero := fun _ => by rw [constantCoeff_map, constantCoeff_act₁, map_zero]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i]
    exact map_homIdentity₁ j (fun _ => constantCoeff_sigmaSeries) (constantCoeff_act₁ a)
      (subst_sigma_act₁ a)

@[simp] theorem rhoEnd_toPowerSeries (a : 𝕆) (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (rhoEnd j a) i = MvPowerSeries.map j (act₁ p a) := rfl

theorem toPowerSeries_fin1 {F : MvFormalGroup 1 B} (e : MvFormalGroup.End F) :
    MvFormalGroup.Hom.toPowerSeries e = fun _ => MvFormalGroup.Hom.toPowerSeries e 0 := by
  funext i; rw [Fin.fin_one_eq_zero i]

def rho : 𝕆 →+* MvFormalGroup.End (sigmaBar j) where
  toFun := rhoEnd j
  map_one' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_one, MvPowerSeries.map_X, MvFormalGroup.End.toPowerSeries_one,
      Fin.fin_one_eq_zero i]
  map_mul' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, MvFormalGroup.End.toPowerSeries_mul, act₁_mul,
      map_subst (hasSubst_fin1 (constantCoeff_act₁ b))]
    rfl
  map_zero' := by
    apply MvFormalGroup.Hom.ext
    funext i
    rw [rhoEnd_toPowerSeries, act₁_zero, map_zero, MvFormalGroup.End.toPowerSeries_zero]
  map_add' a b := by
    apply MvFormalGroup.Hom.ext
    funext i
    have hab : HasSubst (Sum.elim (fun _ : Fin 1 => act₁ p a) fun _ : Fin 1 => act₁ p b) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l) <;> exact constantCoeff_act₁ _
    rw [rhoEnd_toPowerSeries, MvFormalGroup.End.toPowerSeries_add, act₁_add, map_subst hab]
    dsimp only
    rw [sigmaBar_toPowerSeries]
    congr 1
    funext s
    rcases s with l | l <;> rfl

theorem rho_toPowerSeries (a : 𝕆) (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (rho j a) i = MvPowerSeries.map j (act₁ p a) := rfl

theorem coeff_single_rho (a : 𝕆) :
    coeff (Finsupp.single 0 1) (MvFormalGroup.Hom.toPowerSeries (rho j a) 0) = j a := by
  rw [rho_toPowerSeries, coeff_map, coeff_single_act₁]

variable [CharP B p]

theorem rho_p_toPowerSeries :
    MvFormalGroup.Hom.toPowerSeries (rho j (p : 𝕆)) 0 = (X 0 : MvPowerSeries (Fin 1) B) ^ p ^ 2 := by
  rw [rho_toPowerSeries, act₁_natCast_p, map_add, map_mul, map_C, map_natCast, CharP.cast_eq_zero,
    map_zero, zero_mul, zero_add, map_pow, MvPowerSeries.map_X, card_GF]

theorem j_eq_teichmuller (x : 𝕆) : j x = j (WittVector.teichmuller p (x.coeff 0)) := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈ Ideal.span {(p : 𝕆)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  have : j (x - WittVector.teichmuller p (x.coeff 0)) = 0 := by
    rw [← hd, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]
  rwa [map_sub, sub_eq_zero] at this

theorem j_frobenius (x : 𝕆) : j (WittVector.frobenius x) = j x ^ p := by
  rw [j_eq_teichmuller j (WittVector.frobenius x), j_eq_teichmuller j x,
    WittVector.coeff_frobenius_charP, map_pow, map_pow]

theorem map_frobenius_map_j {τ : Type*} (y : MvPowerSeries τ 𝕆) :
    MvPowerSeries.map (frobenius B p) (MvPowerSeries.map j y) =
      MvPowerSeries.map j (MvPowerSeries.map WittVector.frobenius y) := by
  ext m
  simp only [coeff_map, frobenius_def, j_frobenius]

theorem hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero

theorem pow_p_eq_expand_map {τ : Type*} (y : MvPowerSeries τ B) :
    y ^ p = expand p hp0 (MvPowerSeries.map (frobenius B p) y) := by
  rw [← map_frobenius_expand p hp0, map_expand]

theorem sigmaBar_pow_p :
    (MvPowerSeries.map j (sigmaSeries p)) ^ p =
      subst (fun s : Fin 1 ⊕ Fin 1 => (X s : MvPowerSeries (Fin 1 ⊕ Fin 1) B) ^ p)
        (MvPowerSeries.map j (sigmaSeries p)) := by
  rw [pow_p_eq_expand_map, map_frobenius_map_j, map_frobenius_sigmaSeries, expand, coe_substAlgHom]

def phi : MvFormalGroup.End (sigmaBar j) where
  toPowerSeries := fun _ => (X 0 : MvPowerSeries (Fin 1) B) ^ p
  constantCoeff_eq_zero := fun _ => by rw [map_pow, constantCoeff_X, zero_pow hp0]
  subst_eq i := by
    rw [Fin.fin_one_eq_zero i, sigmaBar_toPowerSeries, subst_pow (sigmaBar j).hasSubst_toPowerSeries,
      subst_X (sigmaBar j).hasSubst_toPowerSeries, sigmaBar_toPowerSeries, sigmaBar_pow_p]
    congr 1
    funext s
    rcases s with l | l
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inl,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · rw [Fin.fin_one_eq_zero l, Sum.elim_inr,
        subst_pow (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
        subst_X (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]

@[simp] theorem phi_toPowerSeries (i : Fin 1) :
    MvFormalGroup.Hom.toPowerSeries (phi j) i = (X 0 : MvPowerSeries (Fin 1) B) ^ p := rfl

theorem phi_mul_rho (a : 𝕆) : phi j * rho j a = rho j (WittVector.frobenius a) * phi j := by
  apply MvFormalGroup.Hom.ext
  funext i
  rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul]
  dsimp only
  rw [phi_toPowerSeries,
    subst_pow (rho j a).hasSubst_toPowerSeries, subst_X (rho j a).hasSubst_toPowerSeries,
    rho_toPowerSeries, rho_toPowerSeries, pow_p_eq_expand_map, map_frobenius_map_j, map_frobenius_act₁,
    expand, coe_substAlgHom]
  congr 1
  funext s
  rw [phi_toPowerSeries, Fin.fin_one_eq_zero s]

theorem phi_mul_phi : phi j * phi j = rho j (p : 𝕆) := by
  apply MvFormalGroup.Hom.ext
  funext i
  rw [MvFormalGroup.End.toPowerSeries_mul]
  dsimp only
  rw [phi_toPowerSeries, subst_pow (phi j).hasSubst_toPowerSeries,
    subst_X (phi j).hasSubst_toPowerSeries, phi_toPowerSeries, ← pow_mul, ← sq, Fin.fin_one_eq_zero i,
    rho_p_toPowerSeries]

theorem rho_mul_comm (a b : 𝕆) : rho j a * rho j b = rho j b * rho j a := by
  rw [← map_mul, ← map_mul, mul_comm]

end Reduction

end CerednikDrinfeld.LubinTate

end


