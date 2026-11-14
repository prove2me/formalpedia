-- Prove2me | Definitions.Def_RPLib_S4_CdOneCoh
-- name    : RPLib_S4_CdOneCoh
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T05:01:43.676622+00:00
-- url     : https://prove2.me/theorems/2d7f19dd-4f6a-46da-a5e9-20a992692eed
-- title:
--   Elementary degree-2 group cohomology: cyclic groups and inflation-restriction, with explicit cochains
-- statement:
--   Explicit additive computations in degree 2 for a group $G$ acting on an abelian group $A$ (Mathlib's `groupCohomology.IsCocycle₂` / `IsCoboundary₂`), in any universes. `d₁ b` is the coboundary $(g,h) \mapsto g\,b(h) - b(gh) + b(g)$ of a 1-cochain $b$, and `isCoboundary₂_of_sub` transfers coboundary-ness along $f - d_1 b$. `isCoboundary₂_of_cyclic`: if $\sigma$ generates the finite group $G$ and every $\sigma$-fixed $a \in A$ is a norm $\sum_{t < \operatorname{ord}\sigma} \sigma^t c$, every 2-cocycle is a coboundary. `exists_inflated` (degree-2 inflation-restriction): for $N \trianglelefteq G$ with $H^1(N, A) = 0$ and $f|_{N \times N}$ a coboundary, there is $b$ such that $f - d_1 b$ is a cocycle that is invariant under right multiplication by $N$ in both variables and takes $N$-fixed values (so it is inflated from $G/N$ with values in $A^N$).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Galois cohomology layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, Springer 1979, doi:10.1007/978-1-4757-5673-9, Chapter X, Section 7; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3

import Mathlib

/-!
# S4-PD (3a), part 1: elementary degree-2 group cohomology

Explicit, additive computations behind `Br(L/K) = 0` over a C1 field (no `FiniteCyclic`, any universes):
* `d₁ b`, the coboundary of a 1-cochain; `isCoboundary₂_of_sub` transfers coboundary-ness along `f - d₁ b`.
* `isCoboundary₂_of_cyclic`: if `σ` generates the finite group `G` and every `σ`-fixed element of `A` is a norm
  `∑_{t < ord σ} σ ^ t • c`, every 2-cocycle is a coboundary.
* `exists_inflated` (degree-2 inflation-restriction): for `N ◁ G` with `H¹(N, A) = 0` and `f|N×N` a coboundary,
  `f - d₁ b` is invariant under right multiplication by `N` in both variables and takes `N`-fixed values.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The coboundary of a 1-cochain. -/
def d₁ (b : G → A) : G × G → A := fun p => p.1 • b p.2 - b (p.1 * p.2) + b p.1

@[simp] theorem d₁_apply (b : G → A) (g h : G) : d₁ b (g, h) = g • b h - b (g * h) + b g := rfl

theorem d₁_add (b b' : G → A) : d₁ (b + b') = d₁ b + d₁ b' := by
  funext p; simp only [d₁, Pi.add_apply, smul_add]; abel

theorem eq_of_sub_eq {a b c d : A} (h : c = d) (he : a - b = c - d) : a = b := by
  rw [← sub_eq_zero, he, h, sub_self]

theorem isCocycle₂_d₁ (b : G → A) : IsCocycle₂ (d₁ b) := by
  intro g h j
  simp only [d₁_apply, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

theorem isCocycle₂_sub_d₁ {f : G × G → A} (hf : IsCocycle₂ f) (b : G → A) : IsCocycle₂ (f - d₁ b) := by
  intro g h j
  have h1 := hf g h j
  have h2 := isCocycle₂_d₁ b g h j
  simp only [Pi.sub_apply, smul_sub]
  exact eq_of_sub_eq (congrArg₂ HSub.hSub h1 h2) (by abel)

theorem isCoboundary₂_d₁ (b : G → A) : IsCoboundary₂ (d₁ b) := ⟨b, fun _ _ => rfl⟩

theorem isCoboundary₂_of_sub {f : G × G → A} (b : G → A) (h : IsCoboundary₂ (f - d₁ b)) :
    IsCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  refine ⟨b + x, fun g h => ?_⟩
  have := hx g h
  simp only [Pi.sub_apply, d₁_apply, Pi.add_apply, smul_add] at this ⊢
  rw [eq_sub_iff_add_eq] at this
  rw [← this]; abel

/-! ## The cyclic case -/

section Cyclic

variable [Finite G] {σ : G} (hσ : ∀ g : G, ∃ i : ℕ, σ ^ i = g)

/-- The exponent of `g` in `[0, ord σ)`. -/
noncomputable def idx (g : G) : ℕ := (hσ g).choose % orderOf σ

include hσ in
theorem pow_idx (g : G) : σ ^ idx hσ g = g := by
  rw [idx, pow_mod_orderOf, (hσ g).choose_spec]

theorem idx_lt (g : G) : idx hσ g < orderOf σ :=
  Nat.mod_lt _ (isOfFinOrder_of_finite σ).orderOf_pos

theorem idx_pow {i : ℕ} (hi : i < orderOf σ) : idx hσ (σ ^ i) = i := by
  have h := pow_idx hσ (σ ^ i)
  rw [(isOfFinOrder_of_finite σ).pow_inj_mod, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (idx_lt hσ _)] at h
  exact h

/-- A normalized cocycle on a cyclic group: `F (σ^i, σ^j) = [i + j ≥ m] a`. -/
theorem cyclic_normal_form {F : G × G → A} (hF : IsCocycle₂ F) (hF11 : F (1, 1) = 0)
    (hF0 : ∀ k, k + 1 < orderOf σ → F (σ ^ k, σ) = 0) (i j : ℕ) (hi : i < orderOf σ) (hj : j < orderOf σ) :
    F (σ ^ i, σ ^ j) = if orderOf σ ≤ i + j then F (σ ^ (orderOf σ - 1), σ) else 0 := by
  induction j with
  | zero =>
    rw [if_neg (show ¬ orderOf σ ≤ i + 0 by omega), pow_zero, map_one_snd_of_isCocycle₂ hF (σ ^ i), hF11,
      smul_zero]
  | succ j ih =>
    have hc := hF (σ ^ i) (σ ^ j) σ
    rw [← pow_add, ← pow_succ, hF0 j (by omega), smul_zero, zero_add, ih (by omega)] at hc
    rw [← hc]
    by_cases h1 : i + j + 1 < orderOf σ
    · rw [hF0 _ h1, if_neg (show ¬ orderOf σ ≤ i + j by omega),
        if_neg (show ¬ orderOf σ ≤ i + (j + 1) by omega), add_zero]
    · by_cases h2 : i + j + 1 = orderOf σ
      · rw [if_neg (show ¬ orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega),
          add_zero, show i + j = orderOf σ - 1 by omega]
      · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
        rw [if_pos (show orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega), hr,
          pow_add, pow_orderOf_eq_one, one_mul, hF0 r (by omega), zero_add]

theorem sum_pow_smul_add (c : A) (i j : ℕ) :
    σ ^ i • ∑ t ∈ Finset.range j, σ ^ t • c + ∑ t ∈ Finset.range i, σ ^ t • c =
      ∑ t ∈ Finset.range (i + j), σ ^ t • c := by
  simp only [Finset.sum_range_add, Finset.smul_sum, ← mul_smul, ← pow_add]
  exact add_comm _ _

include hσ in
theorem isCoboundary₂_of_cyclic {f : G × G → A} (hf : IsCocycle₂ f)
    (hnorm : ∀ a : A, σ • a = a → ∃ c : A, ∑ t ∈ Finset.range (orderOf σ), σ ^ t • c = a) :
    IsCoboundary₂ f := by
  classical
  have hm0 : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
  obtain ⟨b, hb⟩ : ∃ b : G → A, ∀ g, b g = f (1, 1) - ∑ t ∈ Finset.range (idx hσ g), f (σ ^ t, σ) :=
    ⟨_, fun _ => rfl⟩
  have hFc : IsCocycle₂ (f - d₁ b) := isCocycle₂_sub_d₁ hf b
  have hb1 : b 1 = f (1, 1) := by
    have h0 : idx hσ 1 = 0 := by simpa using idx_pow hσ (i := 0) hm0
    rw [hb, h0, Finset.sum_range_zero, sub_zero]
  have hF11 : (f - d₁ b) (1, 1) = 0 := by
    simp only [Pi.sub_apply, d₁_apply, one_smul, mul_one, hb1]; abel
  have hF0 : ∀ k, k + 1 < orderOf σ → (f - d₁ b) (σ ^ k, σ) = 0 := by
    intro k hk
    have h1 : idx hσ σ = 1 := by simpa using idx_pow hσ (i := 1) (by omega)
    have hbσ : b σ = 0 := by
      rw [hb, h1, Finset.sum_range_one, pow_zero, map_one_fst_of_isCocycle₂ hf σ, sub_self]
    have hk1 : idx hσ (σ ^ k * σ) = k + 1 := by rw [← pow_succ]; exact idx_pow hσ hk
    have hk0 : idx hσ (σ ^ k) = k := idx_pow hσ (by omega)
    rw [Pi.sub_apply, d₁_apply, hbσ, smul_zero, hb (σ ^ k * σ), hb (σ ^ k), hk1, hk0, Finset.sum_range_succ]
    abel
  have hnf := cyclic_normal_form hFc hF11 hF0
  -- the invariant element `a = F (σ ^ (m - 1), σ)`
  have hσa : σ • (f - d₁ b) (σ ^ (orderOf σ - 1), σ) = (f - d₁ b) (σ ^ (orderOf σ - 1), σ) := by
    by_cases hm1 : orderOf σ = 1
    · rw [orderOf_eq_one_iff.mp hm1, one_smul]
    · have hc := hFc σ (σ ^ (orderOf σ - 1)) σ
      have e1 : σ * σ ^ (orderOf σ - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e2 : σ ^ (orderOf σ - 1) * σ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e3 := hnf 1 (orderOf σ - 1) (by omega) (by omega)
      rw [pow_one, if_pos (show orderOf σ ≤ 1 + (orderOf σ - 1) by omega)] at e3
      rw [e1, e2, map_one_fst_of_isCocycle₂ hFc σ, hF11, zero_add, e3,
        map_one_snd_of_isCocycle₂ hFc σ, hF11, smul_zero, add_zero] at hc
      exact hc.symm
  obtain ⟨c, hcn⟩ := hnorm _ hσa
  obtain ⟨b', hb'⟩ : ∃ b' : G → A, ∀ g, b' g = ∑ t ∈ Finset.range (idx hσ g), σ ^ t • c :=
    ⟨_, fun _ => rfl⟩
  apply isCoboundary₂_of_sub b
  refine ⟨b', fun g h => ?_⟩
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < orderOf σ ∧ σ ^ i = g := ⟨_, idx_lt hσ g, pow_idx hσ g⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < orderOf σ ∧ σ ^ j = h := ⟨_, idx_lt hσ h, pow_idx hσ h⟩
  rw [hnf i j hi hj, ← pow_add, hb', hb', hb', idx_pow hσ hi, idx_pow hσ hj]
  by_cases hij : orderOf σ ≤ i + j
  · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
    rw [if_pos hij, hr, pow_add, pow_orderOf_eq_one, one_mul, idx_pow hσ (by omega : r < orderOf σ),
      sub_add_eq_add_sub, sum_pow_smul_add, hr, Finset.sum_range_add, hcn]
    simp only [pow_add, pow_orderOf_eq_one, one_mul, add_sub_cancel_right]
  · rw [if_neg hij, idx_pow hσ (by omega : i + j < orderOf σ), sub_add_eq_add_sub, sum_pow_smul_add,
      sub_self]

end Cyclic

/-! ## Inflation-restriction in degree 2 -/

section InfRes

variable (N : Subgroup G) [hN : N.Normal]

/-- A representative of the coset `g N`. -/
noncomputable def rep (g : G) : G := (QuotientGroup.mk g : G ⧸ N).out

theorem rep_inv_mul_mem (g : G) : (rep N g)⁻¹ * g ∈ N :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

theorem rep_eq_of_mem {g g' : G} (h : g⁻¹ * g' ∈ N) : rep N g = rep N g' := by
  unfold rep; rw [QuotientGroup.eq.mpr h]

theorem rep_mul_mem (g : G) {n : G} (hn : n ∈ N) : rep N (g * n) = rep N g :=
  rep_eq_of_mem N (by simpa [mul_assoc] using N.inv_mem hn)

theorem rep_mem_of_mem {n : G} (hn : n ∈ N) : rep N n ∈ N := by
  have h := N.mul_mem (rep_inv_mul_mem N n) (N.inv_mem hn)
  rw [mul_inv_cancel_right] at h
  simpa using N.inv_mem h

theorem rep_of_mem {n : G} (hn : n ∈ N) : rep N n = rep N 1 :=
  rep_eq_of_mem N (by simpa using N.inv_mem hn)

include hN in
theorem conj_mem' {n : G} (hn : n ∈ N) (h : G) : h⁻¹ * n * h ∈ N := by
  simpa using hN.conj_mem n hn h⁻¹

include hN in
theorem rep_mem_mul {n : G} (hn : n ∈ N) (h : G) : rep N (n * h) = rep N h := by
  refine rep_eq_of_mem N ?_
  have := conj_mem' N (N.inv_mem hn) h
  convert this using 1; group

theorem exists_zero_on_sub {f : G × G → A}
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, ∀ n ∈ N, ∀ n' ∈ N, (f - d₁ b) (n, n') = 0 := by
  classical
  obtain ⟨β, hβ⟩ := hNf
  refine ⟨fun g => if h : g ∈ N then β ⟨g, h⟩ else 0, fun n hn n' hn' => ?_⟩
  have e : n • β ⟨n', hn'⟩ - β ⟨n * n', N.mul_mem hn hn'⟩ + β ⟨n, hn⟩ = f (n, n') :=
    hβ ⟨n, hn⟩ ⟨n', hn'⟩
  simp only [Pi.sub_apply, d₁_apply, dif_pos hn, dif_pos hn', dif_pos (N.mul_mem hn hn')]
  rw [e, sub_self]

theorem exists_zero_right {f : G × G → A} (hf : IsCocycle₂ f)
    (h0 : ∀ n ∈ N, ∀ n' ∈ N, f (n, n') = 0) :
    ∃ b : G → A, ∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0 := by
  refine ⟨fun g => -f (rep N g, (rep N g)⁻¹ * g), fun g n hn => ?_⟩
  have hbn : f (rep N n, (rep N n)⁻¹ * n) = 0 :=
    h0 _ (rep_mem_of_mem N hn) _ (rep_inv_mul_mem N n)
  have hgn : rep N (g * n) = rep N g := rep_mul_mem N g hn
  have hc := hf (rep N g) ((rep N g)⁻¹ * g) n
  rw [mul_inv_cancel_left, h0 _ (rep_inv_mul_mem N g) _ hn, smul_zero, zero_add,
    mul_assoc ((rep N g)⁻¹) g n] at hc
  simp only [Pi.sub_apply, d₁_apply, hgn, hbn, neg_zero, smul_zero]
  rw [← hc]; abel

include hN in
theorem exists_zero_both {f : G × G → A} (hf : IsCocycle₂ f) (h1 : ∀ g, ∀ n ∈ N, f (g, n) = 0)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ) :
    ∃ b : G → A, (∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0) ∧ ∀ n ∈ N, ∀ h, (f - d₁ b) (n, h) = 0 := by
  classical
  have hfR : ∀ g h, ∀ n ∈ N, f (g, h * n) = f (g, h) := by
    intro g h n hn
    have := hf g h n
    rw [h1 _ n hn, h1 h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hcoc : ∀ k : G, IsCocycle₁ (fun n : N => f ((n : G), k)) := by
    intro k n n'
    have hc := hf n n' k
    rw [h1 _ _ n'.2, add_zero] at hc
    have e : f ((n : G), (n' : G) * k) = f (n, k) := by
      rw [show (n' : G) * k = k * (k⁻¹ * n' * k) by group]
      exact hfR _ _ _ (conj_mem' N n'.2 k)
    rw [e] at hc
    exact hc
  choose c hc using fun k : G => hH1 _ (hcoc k)
  have hc' : ∀ k, ∀ n ∈ N, n • c k - c k = f (n, k) := fun k n hn => hc k ⟨n, hn⟩
  refine ⟨fun h => c (rep N h) - c (rep N 1), fun g n hn => ?_, fun n hn h => ?_⟩
  · simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mul_mem N g hn, sub_self, smul_zero,
      h1 g n hn]
    abel
  · have hfn : f (n, h) = f (n, rep N h) := by
      conv_lhs => rw [← mul_inv_cancel_left (rep N h) h]
      exact hfR _ _ _ (rep_inv_mul_mem N h)
    have hf1 : f (n, rep N 1) = 0 := h1 n _ (rep_mem_of_mem N (one_mem N))
    simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mem_mul N hn, sub_self, add_zero, smul_sub]
    have h0' : n • c (rep N 1) - c (rep N 1) = 0 := by rw [hc' _ n hn, hf1]
    rw [hfn, ← hc' _ n hn]
    exact eq_of_sub_eq h0' (by abel)

include hN in
theorem invariant_of_zero {F : G × G → A} (hF : IsCocycle₂ F) (hR : ∀ g, ∀ n ∈ N, F (g, n) = 0)
    (hL : ∀ n ∈ N, ∀ h, F (n, h) = 0) (g h : G) {n : G} (hn : n ∈ N) :
    F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧ n • F (g, h) = F (g, h) := by
  have hright : ∀ g h, ∀ n ∈ N, F (g, h * n) = F (g, h) := by
    intro g h n hn
    have := hF g h n
    rw [hR _ n hn, hR h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hleft : ∀ g h, ∀ n ∈ N, F (g * n, h) = F (g, h) := by
    intro g h n hn
    have := hF g n h
    rw [hR g n hn, hL n hn h, smul_zero, zero_add, add_zero,
      show n * h = h * (h⁻¹ * n * h) by group] at this
    rw [this]; exact hright _ _ _ (conj_mem' N hn h)
  refine ⟨hleft g h n hn, hright g h n hn, ?_⟩
  have := hF n g h
  rw [hL n hn g, hL n hn (g * h), add_zero, add_zero, show n * g = g * (g⁻¹ * n * g) by group,
    hleft _ _ _ (conj_mem' N hn g)] at this
  exact this.symm

include hN in
/-- Degree-2 inflation-restriction: `f` is cohomologous to a cocycle inflated from `G ⧸ N` with values in `A^N`. -/
theorem exists_inflated {f : G × G → A} (hf : IsCocycle₂ f)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ)
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, IsCocycle₂ (f - d₁ b) ∧ ∀ g h : G, ∀ n ∈ N,
      (f - d₁ b) (g * n, h) = (f - d₁ b) (g, h) ∧ (f - d₁ b) (g, h * n) = (f - d₁ b) (g, h) ∧
        n • (f - d₁ b) (g, h) = (f - d₁ b) (g, h) := by
  obtain ⟨b0, hb0⟩ := exists_zero_on_sub N hNf
  have hf0 := isCocycle₂_sub_d₁ hf b0
  obtain ⟨b1, hb1⟩ := exists_zero_right N hf0 hb0
  have hf1 := isCocycle₂_sub_d₁ hf0 b1
  obtain ⟨b2, hb2R, hb2L⟩ := exists_zero_both N hf1 hb1 hH1
  have hf2 := isCocycle₂_sub_d₁ hf1 b2
  have e : f - d₁ (b0 + b1 + b2) = f - d₁ b0 - d₁ b1 - d₁ b2 := by
    rw [d₁_add, d₁_add]; abel
  refine ⟨b0 + b1 + b2, ?_, fun g h n hn => ?_⟩
  · rw [e]; exact hf2
  · rw [e]; exact invariant_of_zero N hf2 hb2R hb2L g h hn

end InfRes

end RamanujanPetersson.CdOne


