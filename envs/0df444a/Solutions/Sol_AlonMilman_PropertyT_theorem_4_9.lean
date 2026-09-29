-- Prove2me | solution 1 for AlonMilman.PropertyT.theorem_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T10:56:19.364102+00:00
-- url     : https://prove2.me/submissions/e6087cf3-3775-4dba-8b7a-aad1163dfd9b

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_HasPropertyT
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian
import Definitions.Def_AlonMilman_PropertyT_IsEnlarger
import Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph

set_option autoImplicit false

/-- Dirichlet energy of `f` along left translation by `g`. -/
noncomputable def e66D {T : Type} [Group T] [Fintype T] (g : T) (f : T → ℝ) : ℝ :=
  ∑ u, (f (g * u) - f u) ^ 2

theorem e66D_nonneg {T : Type} [Group T] [Fintype T] (g : T) (f : T → ℝ) : 0 ≤ e66D g f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem e66D_one {T : Type} [Group T] [Fintype T] (f : T → ℝ) : e66D 1 f = 0 := by
  simp [e66D]

theorem e66D_inv {T : Type} [Group T] [Fintype T] (g : T) (f : T → ℝ) :
    e66D g⁻¹ f = e66D g f := by
  unfold e66D
  refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
  ring

theorem e66D_mul {T : Type} [Group T] [Fintype T] (a b : T) (f : T → ℝ) :
    e66D (a * b) f ≤ 2 * e66D a f + 2 * e66D b f := by
  have h1 : ∑ u, (f (a * (b * u)) - f (b * u)) ^ 2 = e66D a f := by
    unfold e66D
    exact Fintype.sum_equiv (Equiv.mulLeft b) _ _ (fun u => by simp)
  rw [← h1]
  unfold e66D
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [mul_assoc]
  nlinarith [sq_nonneg (f (a * (b * u)) - 2 * f (b * u) + f u)]

theorem e66D_eq {T : Type} [Group T] [Fintype T] (g : T) (f : T → ℝ) :
    e66D g f = 2 * ∑ u, f u ^ 2 - 2 * ∑ u, f (g * u) * f u := by
  have h1 : ∑ u, f (g * u) ^ 2 = ∑ u, f u ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun u => by simp)
  have h2 : e66D g f = ∑ u, f (g * u) ^ 2 + ∑ u, f u ^ 2 - 2 * ∑ u, f (g * u) * f u := by
    unfold e66D
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [h2, h1]
  ring

theorem e66_row {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T] (φ : H →* T)
    (S : Finset H) (w : T) (g : T → ℝ) :
    ∑ u, ((AlonMilman.PropertyT.cayleyMultigraph φ S w u : ℕ) : ℝ) * g u
      = ∑ s ∈ S, g ((φ s)⁻¹ * w) := by
  simp only [AlonMilman.PropertyT.cayleyMultigraph, Finset.natCast_card_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single ((φ s)⁻¹ * w)]
  · simp
  · intro u _ hu
    have hne : ¬ (w * u⁻¹ = φ s) := by
      intro h
      apply hu
      rw [← h]
      group
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Matrix in
theorem e66_quad {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T] (φ : H →* T)
    (S : Finset H) (f : T → ℝ) :
    f ⬝ᵥ (AlonMilman.PropertyT.laplacian (AlonMilman.PropertyT.cayleyMultigraph φ S) *ᵥ f)
      = (1 / 2) * ∑ s ∈ S, e66D (φ s) f := by
  have hdeg : ∀ w, ∑ u, ((AlonMilman.PropertyT.cayleyMultigraph φ S w u : ℕ) : ℝ) = S.card := by
    intro w
    have h := e66_row φ S w (fun _ => 1)
    simpa using h
  have hA : ∀ w, ((AlonMilman.PropertyT.cayleyMultigraph φ S).map (fun m : ℕ => (m : ℝ)) *ᵥ f) w
      = ∑ s ∈ S, f ((φ s)⁻¹ * w) := by
    intro w
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact e66_row φ S w f
  have hD : ∀ w, (Matrix.diagonal (fun v => ∑ u,
      ((AlonMilman.PropertyT.cayleyMultigraph φ S v u : ℕ) : ℝ)) *ᵥ f) w = S.card * f w := by
    intro w
    rw [Matrix.mulVec_diagonal, hdeg]
  have hre : ∀ s ∈ S, ∑ u, f (φ s * u) * f u = ∑ w, f w * f ((φ s)⁻¹ * w) := by
    intro s _
    exact Fintype.sum_equiv (Equiv.mulLeft (φ s)) _ _ (fun u => by simp)
  have e1 : ∑ w, f w * ((S.card : ℝ) * f w) = S.card * ∑ u, f u ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have e2 : ∑ w, f w * ∑ s ∈ S, f ((φ s)⁻¹ * w) = ∑ s ∈ S, ∑ u, f (φ s * u) * f u := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    exact (hre s hs).symm
  have e3 : ∑ s ∈ S, e66D (φ s) f
      = 2 * S.card * ∑ u, f u ^ 2 - 2 * ∑ s ∈ S, ∑ u, f (φ s * u) * f u := by
    simp only [e66D_eq, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [AlonMilman.PropertyT.laplacian, Matrix.sub_mulVec, dotProduct_sub]
  have l1 : f ⬝ᵥ (Matrix.diagonal (fun v => ∑ u,
      ((AlonMilman.PropertyT.cayleyMultigraph φ S v u : ℕ) : ℝ)) *ᵥ f)
      = ∑ w, f w * ((S.card : ℝ) * f w) := by
    simp only [dotProduct, hD]
  have l2 : f ⬝ᵥ ((AlonMilman.PropertyT.cayleyMultigraph φ S).map (fun m : ℕ => (m : ℝ)) *ᵥ f)
      = ∑ w, f w * ∑ s ∈ S, f ((φ s)⁻¹ * w) := by
    simp only [dotProduct, hA]
  rw [l1, l2, e1, e2, e3]
  ring

theorem e66_symm {H T : Type} [Group H] [Group T] [DecidableEq T] (φ : H →* T) (S : Finset H)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (w u : T) :
    AlonMilman.PropertyT.cayleyMultigraph φ S w u
      = AlonMilman.PropertyT.cayleyMultigraph φ S u w := by
  unfold AlonMilman.PropertyT.cayleyMultigraph
  apply Finset.card_nbij' (fun s => s⁻¹) (fun s => s⁻¹)
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter] at hs ⊢
    refine ⟨hSinv s hs.1, ?_⟩
    rw [map_inv, ← hs.2]
    group
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter] at hs ⊢
    refine ⟨hSinv s hs.1, ?_⟩
    rw [map_inv, ← hs.2]
    group
  · intro s _
    simp
  · intro s _
    simp

theorem e66_herm {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T] (φ : H →* T)
    (S : Finset H) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) :
    (AlonMilman.PropertyT.laplacian (AlonMilman.PropertyT.cayleyMultigraph φ S)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro w u
  rw [star_trivial]
  simp only [AlonMilman.PropertyT.laplacian, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.map_apply]
  rw [e66_symm φ S hSinv u w]
  by_cases h : u = w
  · subst h; rfl
  · simp [h, Ne.symm h]

open Matrix in
theorem e66_homog {n : Type} [Fintype n] (Q : Matrix n n ℝ) (c : ℝ)
    (H : ∀ x : n → ℝ, ∑ u, x u = 0 → x ⬝ᵥ x = 1 → c ≤ x ⬝ᵥ (Q *ᵥ x)) :
    ∀ x : n → ℝ, ∑ u, x u = 0 → c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x) := by
  intro x hx
  by_cases h0 : x = 0
  · subst h0; simp
  · have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
    have hpos : 0 < x ⬝ᵥ x := by
      rcases lt_or_eq_of_le hnn with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) h0
    obtain ⟨s, hs⟩ : ∃ s, s = x ⬝ᵥ x := ⟨_, rfl⟩
    rw [← hs] at hpos ⊢
    obtain ⟨t, ht⟩ : ∃ t, t = (Real.sqrt s)⁻¹ := ⟨_, rfl⟩
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hpos.le
    have htt : t * t * s = 1 := by
      rw [ht, ← mul_inv, hsq, inv_mul_cancel₀ hpos.ne']
    have hsum : ∑ u, (t • x) u = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]
    have hunit : (t • x) ⬝ᵥ (t • x) = 1 := by
      simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← hs]
      linarith [htt]
    have h1 := H (t • x) hsum hunit
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    have key : t * (t * (x ⬝ᵥ (Q *ᵥ x))) * s = x ⬝ᵥ (Q *ᵥ x) := by
      calc t * (t * (x ⬝ᵥ (Q *ᵥ x))) * s = (x ⬝ᵥ (Q *ᵥ x)) * (t * t * s) := by ring
        _ = _ := by rw [htt, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le]

open Matrix in
theorem e66_eig {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ) (hQ : Q.IsHermitian)
    (hn : 2 ≤ Fintype.card n) (c : ℝ)
    (H : ∀ x : n → ℝ, ∑ u, x u = 0 → c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x)) :
    c ≤ AlonMilman.PropertyT.lambda1 Q := by
  unfold AlonMilman.PropertyT.lambda1
  rw [dif_pos ⟨hQ, hn⟩]
  have hi1 : Fintype.card n - 2 < Fintype.card n := by omega
  have hi2 : Fintype.card n - 1 < Fintype.card n := by omega
  show c ≤ hQ.eigenvalues₀ ⟨Fintype.card n - 2, hi1⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (Fintype.card n) ≃ n,
      e = Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) := ⟨_, rfl⟩
  have hev : ∀ j, hQ.eigenvalues (e j) = hQ.eigenvalues₀ j := by
    intro j
    rw [he]
    simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  have hmono : hQ.eigenvalues₀ ⟨Fintype.card n - 1, hi2⟩
      ≤ hQ.eigenvalues₀ ⟨Fintype.card n - 2, hi1⟩ :=
    hQ.eigenvalues₀_antitone (show (⟨Fintype.card n - 2, hi1⟩ : Fin (Fintype.card n))
      ≤ ⟨Fintype.card n - 1, hi2⟩ from by simp only [Fin.mk_le_mk]; omega)
  obtain ⟨μ1, hμ1⟩ : ∃ μ, μ = hQ.eigenvalues₀ ⟨Fintype.card n - 2, hi1⟩ := ⟨_, rfl⟩
  obtain ⟨μ2, hμ2⟩ : ∃ μ, μ = hQ.eigenvalues₀ ⟨Fintype.card n - 1, hi2⟩ := ⟨_, rfl⟩
  rw [← hμ1]
  rw [← hμ1, ← hμ2] at hmono
  have horth := orthonormal_iff_ite.mp hQ.eigenvectorBasis.orthonormal
  have hdot : ∀ i j, WithLp.ofLp (hQ.eigenvectorBasis i) ⬝ᵥ WithLp.ofLp (hQ.eigenvectorBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have := horth i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    rw [← this, dotProduct_comm]
    simp
  have hne : e ⟨Fintype.card n - 2, hi1⟩ ≠ e ⟨Fintype.card n - 1, hi2⟩ := by
    intro h
    have := e.injective h
    simp only [Fin.mk.injEq] at this
    omega
  obtain ⟨v1, hv1⟩ : ∃ v, v = WithLp.ofLp (hQ.eigenvectorBasis (e ⟨Fintype.card n - 2, hi1⟩)) :=
    ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v, v = WithLp.ofLp (hQ.eigenvectorBasis (e ⟨Fintype.card n - 1, hi2⟩)) :=
    ⟨_, rfl⟩
  have ev1 : Q *ᵥ v1 = μ1 • v1 := by
    rw [hv1, hQ.mulVec_eigenvectorBasis, hev, hμ1]
  have ev2 : Q *ᵥ v2 = μ2 • v2 := by
    rw [hv2, hQ.mulVec_eigenvectorBasis, hev, hμ2]
  have o11 : v1 ⬝ᵥ v1 = 1 := by rw [hv1, hdot]; simp
  have o22 : v2 ⬝ᵥ v2 = 1 := by rw [hv2, hdot]; simp
  have o12 : v1 ⬝ᵥ v2 = 0 := by rw [hv1, hv2, hdot]; simp [hne]
  have o21 : v2 ⬝ᵥ v1 = 0 := by rw [dotProduct_comm]; exact o12
  by_cases ha : ∑ u, v1 u = 0
  · have h := H v1 ha
    rw [ev1, dotProduct_smul, o11, smul_eq_mul] at h
    linarith
  · obtain ⟨a, haa⟩ : ∃ a, a = ∑ u, v1 u := ⟨_, rfl⟩
    obtain ⟨b, hbb⟩ : ∃ b, b = ∑ u, v2 u := ⟨_, rfl⟩
    rw [← haa] at ha
    have hx : ∑ u, (b • v1 - a • v2) u = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← haa, ← hbb]
      ring
    have h := H (b • v1 - a • v2) hx
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ev1, ev2] at h
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      o11, o22, o12, o21] at h
    have hpos : 0 < a ^ 2 + b ^ 2 := by
      have : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
      nlinarith [sq_nonneg b]
    have h' : c * (a ^ 2 + b ^ 2) ≤ μ1 * (a ^ 2 + b ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hmono (sq_nonneg a)]
    exact le_of_mul_le_mul_right h' hpos

/-- The subspace of mean-zero vectors of `ℓ²(T)`. -/
noncomputable def e66W (T : Type) [Fintype T] : Submodule ℂ (EuclideanSpace ℂ T) where
  carrier := {x | ∑ u, x u = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Finset.sum_add_distrib, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp [← Finset.mul_sum, hx]

theorem e66W_mem {T : Type} [Fintype T] (x : EuclideanSpace ℂ T) :
    x ∈ e66W T ↔ ∑ u, x u = 0 := Iff.rfl

/-- Left translation on `ℓ²(T)`. -/
noncomputable def e66L {T : Type} [Group T] [Fintype T] (g : T) :
    EuclideanSpace ℂ T ≃ₗᵢ[ℂ] EuclideanSpace ℂ T :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)

theorem e66L_apply {T : Type} [Group T] [Fintype T] (g : T) (x : EuclideanSpace ℂ T) (u : T) :
    e66L g x u = x (g⁻¹ * u) := by
  simp [e66L, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem e66L_mem {T : Type} [Group T] [Fintype T] (g : T) (x : EuclideanSpace ℂ T)
    (hx : x ∈ e66W T) : e66L g x ∈ e66W T := by
  rw [e66W_mem] at hx ⊢
  simp only [e66L_apply]
  have : ∑ u, x (g⁻¹ * u) = ∑ u, x u :=
    Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun u => by simp)
  rw [this]
  exact hx

/-- Left translation restricted to the mean-zero subspace. -/
noncomputable def e66R {T : Type} [Group T] [Fintype T] (g : T) : e66W T ≃ₗᵢ[ℂ] e66W T where
  toFun x := ⟨e66L g x, e66L_mem g x x.2⟩
  invFun x := ⟨e66L g⁻¹ x, e66L_mem g⁻¹ x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp
  left_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro u
    simp [e66L_apply]
  right_inv x := by
    apply Subtype.ext
    apply PiLp.ext
    intro u
    simp [e66L_apply]
  norm_map' x := by
    show ‖e66L g (x : EuclideanSpace ℂ T)‖ = ‖(x : EuclideanSpace ℂ T)‖
    exact LinearIsometryEquiv.norm_map _ _

theorem e66R_coord {T : Type} [Group T] [Fintype T] (g : T) (x : e66W T) (u : T) :
    ((e66R g x : e66W T) : EuclideanSpace ℂ T) u = (x : EuclideanSpace ℂ T) (g⁻¹ * u) := by
  show e66L g (x : EuclideanSpace ℂ T) u = _
  rw [e66L_apply]

theorem e66R_mul {T : Type} [Group T] [Fintype T] (a b : T) :
    e66R (a * b) = e66R a * e66R b := by
  apply LinearIsometryEquiv.ext
  intro x
  apply Subtype.ext
  apply PiLp.ext
  intro u
  rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
  simp only [e66R_coord, mul_inv_rev, mul_assoc]

/-- The (pulled-back) left regular representation on mean-zero functions. -/
noncomputable def e66ρ {H T : Type} [Group H] [Group T] [Fintype T] (φ : H →* T) :
    H →* (e66W T ≃ₗᵢ[ℂ] e66W T) where
  toFun h := e66R (φ h)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    apply Subtype.ext
    apply PiLp.ext
    intro u
    show ((e66R (φ 1) x : e66W T) : EuclideanSpace ℂ T) u = (x : EuclideanSpace ℂ T) u
    rw [e66R_coord, map_one, inv_one, one_mul]
  map_mul' a b := by
    simp only [map_mul]
    exact e66R_mul _ _

open AlonMilman.PropertyT in
theorem e66_propT {H T : Type} [Group H] [Group T] [Fintype T] (φ : H →* T)
    (hφ : Function.Surjective φ) (ε₀ : ℝ) (K : Finset H)
    (hK : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : H →* unitary (V →L[ℂ] V)), EssentiallyNontrivial π →
      ∀ y : V, ‖y‖ = 1 → ∃ h ∈ K, ‖inner ℂ ((π h : V →L[ℂ] V) y) y‖ < 1 - ε₀)
    (f : T → ℝ) (hf0 : ∑ u, f u = 0) (hf1 : ∑ u, f u ^ 2 = 1) :
    ∃ h ∈ K, ∑ u, f ((φ h)⁻¹ * u) * f u < 1 - ε₀ := by
  let π := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := e66W T)).symm.toMonoidHom.comp (e66ρ φ)
  have hπ : ∀ (h : H) (y : e66W T), (((π h).val y : e66W T) :
      EuclideanSpace ℂ T) = e66L (φ h) (y : EuclideanSpace ℂ T) := fun h y => rfl
  have hEN : EssentiallyNontrivial π := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    apply hv
    have hc : ∀ u, (v : EuclideanSpace ℂ T) u = (v : EuclideanSpace ℂ T) 1 := by
      intro u
      obtain ⟨h, hh⟩ := hφ u⁻¹
      have h1 := congrArg (fun w : e66W T => (w : EuclideanSpace ℂ T) 1) (hcon h)
      simp only [hπ, e66L_apply, hh, inv_inv, mul_one] at h1
      exact h1
    have hsum : ∑ u, (v : EuclideanSpace ℂ T) u = 0 := (e66W_mem _).mp v.2
    have hsum' : ∑ u, (v : EuclideanSpace ℂ T) u = ∑ _u : T, (v : EuclideanSpace ℂ T) 1 :=
      Finset.sum_congr rfl (fun u _ => hc u)
    rw [hsum', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hcard : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h1 : (v : EuclideanSpace ℂ T) 1 = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h hcard
      · exact h
    apply Subtype.ext
    apply PiLp.ext
    intro u
    rw [hc u, h1]
    simp
  have hXmem : (WithLp.toLp 2 (fun u => (f u : ℂ)) : EuclideanSpace ℂ T) ∈ e66W T := by
    rw [e66W_mem]
    simp only [PiLp.toLp_apply]
    exact_mod_cast hf0
  obtain ⟨y, hyX⟩ : ∃ y : e66W T,
      (y : EuclideanSpace ℂ T) = WithLp.toLp 2 (fun u => (f u : ℂ)) := ⟨⟨_, hXmem⟩, rfl⟩
  have hyc : ∀ u, (y : EuclideanSpace ℂ T) u = (f u : ℂ) := by
    intro u
    rw [hyX]
  have hy : ‖y‖ = 1 := by
    have : ‖y‖ = ‖(y : EuclideanSpace ℂ T)‖ := rfl
    rw [this, EuclideanSpace.norm_eq]
    simp only [hyc, Complex.norm_real, Real.norm_eq_abs, sq_abs, hf1, Real.sqrt_one]
  obtain ⟨h, hhK, hlt⟩ := hK (e66W T) π hEN y hy
  refine ⟨h, hhK, ?_⟩
  rw [Submodule.coe_inner, hπ, PiLp.inner_apply] at hlt
  simp only [e66L_apply, hyc] at hlt
  have hre : ∑ u, inner ℂ ((f ((φ h)⁻¹ * u) : ℂ)) ((f u : ℂ))
      = ((∑ u, f ((φ h)⁻¹ * u) * f u : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro u _
    simp only [RCLike.inner_apply, Complex.conj_ofReal]
    try ring
  rw [hre, Complex.norm_real, Real.norm_eq_abs] at hlt
  exact lt_of_le_of_lt (le_abs_self _) hlt

open AlonMilman.PropertyT Matrix in
theorem solution {H : Type} [Group H] (hH : HasPropertyT H) (S : Finset H)
    (hS : Subgroup.closure (S : Set H) = ⊤) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (T : ℕ → Type) [∀ i, Group (T i)] [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (φ : ∀ i, H →* T i) (hφ : ∀ i, Function.Surjective (φ i))
    (hcard : Filter.Tendsto (fun i => Fintype.card (T i)) Filter.atTop Filter.atTop) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 2 ≤ Fintype.card (T i) →
      IsEnlarger (Fintype.card (T i)) S.card ε (cayleyMultigraph (φ i) S) := by
  obtain ⟨ε₀, hε₀, K, hK⟩ := hH
  have hP : ∀ x : H, ∃ C : ℝ, 0 ≤ C ∧ ∀ i (f : T i → ℝ),
      e66D (φ i x) f ≤ C * ∑ s ∈ S, e66D (φ i s) f := by
    intro x
    have hx : x ∈ Subgroup.closure (S : Set H) := by rw [hS]; exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine ⟨1, zero_le_one, fun i f => ?_⟩
      rw [one_mul]
      exact Finset.single_le_sum (f := fun s => e66D (φ i s) f)
        (fun s _ => e66D_nonneg _ _) hx
    | one =>
      refine ⟨0, le_rfl, fun i f => ?_⟩
      rw [map_one, e66D_one, zero_mul]
    | mul x y _ _ hx hy =>
      obtain ⟨C1, hC1, h1⟩ := hx
      obtain ⟨C2, hC2, h2⟩ := hy
      refine ⟨2 * C1 + 2 * C2, by positivity, fun i f => ?_⟩
      rw [map_mul]
      have k0 := e66D_mul (φ i x) (φ i y) f
      have k1 := h1 i f
      have k2 := h2 i f
      nlinarith
    | inv x _ hx =>
      obtain ⟨C, hC, h⟩ := hx
      exact ⟨C, hC, fun i f => by rw [map_inv, e66D_inv]; exact h i f⟩
  choose C hC0 hC using hP
  obtain ⟨CK, hCK⟩ : ∃ CK : ℝ, CK = 1 + ∑ h ∈ K, C h⁻¹ := ⟨_, rfl⟩
  have hCK1 : 1 ≤ CK := by
    have : 0 ≤ ∑ h ∈ K, C h⁻¹ := Finset.sum_nonneg (fun h _ => hC0 _)
    linarith
  have hCKpos : 0 < CK := by linarith
  have hCle : ∀ h ∈ K, C h⁻¹ ≤ CK := by
    intro h hh
    have := Finset.single_le_sum (f := fun h => C h⁻¹) (fun h _ => hC0 _) hh
    linarith
  refine ⟨ε₀ / CK, div_pos hε₀ hCKpos, fun i hi => ?_⟩
  have hunit : ∀ f : T i → ℝ, ∑ u, f u = 0 → f ⬝ᵥ f = 1 →
      ε₀ / CK ≤ f ⬝ᵥ (laplacian (cayleyMultigraph (φ i) S) *ᵥ f) := by
    intro f hf0 hf1
    have hsq : ∑ u, f u ^ 2 = 1 := by
      rw [← hf1]
      simp only [dotProduct, sq]
    obtain ⟨h, hK', hlt⟩ := e66_propT (φ i) (hφ i) ε₀ K hK f hf0 hsq
    rw [e66_quad]
    have hD := e66D_eq (φ i h)⁻¹ f
    have hbound := hC h⁻¹ i f
    rw [map_inv] at hbound
    have hSig : 0 ≤ ∑ s ∈ S, e66D (φ i s) f := Finset.sum_nonneg (fun s _ => e66D_nonneg _ _)
    have hCh := hCle h hK'
    have h2 : 2 * ε₀ < CK * ∑ s ∈ S, e66D (φ i s) f := by
      nlinarith [mul_le_mul_of_nonneg_right hCh hSig]
    rw [div_le_iff₀ hCKpos]
    nlinarith
  have hQ := e66_herm (φ i) S hSinv
  unfold IsEnlarger
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Matrix.IsSymm.ext (fun w u => e66_symm (φ i) S hSinv u w)
  · intro u
    have h := e66_row (φ i) S u (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
    exact_mod_cast h
  · exact e66_eig _ hQ hi _ (e66_homog _ _ hunit)
