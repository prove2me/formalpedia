-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_HeckeRepresentatives
-- name    : LanglandsTunnell_CubicInduction_HeckeRepresentatives
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/2fc224e9-5ba3-54aa-8708-2e05f8cf8d55
-- title:
--   Explicit Hecke coset representatives for GL₃ at a finite place
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ and write $N(v)=\mathrm{absNorm}(v)$, $\varpi$ for the chosen uniformizer `varpi v` of the completion $\mathbb{Q}_v$, and $n(x,y,z)$ for `upperUnipotent3`, the upper triangular unipotent with $(1,2)$-entry $x$, $(2,3)$-entry $y$ and $(1,3)$-entry $z$. `digit v` sends $d\in\{0,\dots,N(v)-1\}$ to the image of the natural number $d$ in $\mathbb{Q}_v$. For an arbitrary map `dig : α → ℚ_v`, two families indexed by $(\alpha\times\alpha)\oplus\alpha\oplus\{*\}$ are defined. `heckeGen1Reps` sends $(a,b)$ to $n(\mathrm{dig}\,a,0,\mathrm{dig}\,b)\cdot\mathrm{diag}(N(v),1,1)$, sends $c$ to $n(0,\mathrm{dig}\,c,0)\cdot\mathrm{diag}(1,N(v),1)$, and sends the point to `centralGen v * (heckeGen2 v)⁻¹`, that is $\mathrm{diag}(\varpi,\varpi,\varpi)\,\mathrm{diag}(\varpi,\varpi,1)^{-1}$; here the diagonal blocks are the matrices `twoRowPointLocal`, built from the rational integer $N(v)$. `heckeGen2Reps` sends $(b,c)$ to $n(0,\mathrm{dig}\,c,\mathrm{dig}\,b)\cdot\mathrm{diag}(N(v),N(v),1)$, sends $a$ to $n(\mathrm{dig}\,a,0,0)\cdot\bigl(\mathrm{diag}(N(v),1,1)\cdot\mathrm{diag}(\varpi,\varpi,\varpi)\mathrm{diag}(\varpi,\varpi,1)^{-1}\bigr)$, and sends the point to $\mathrm{diag}(1,N(v),1)\cdot\mathrm{diag}(\varpi,\varpi,\varpi)\mathrm{diag}(\varpi,\varpi,1)^{-1}$. Six equations record these values, `repIndexEquiv p` is a bijection $(\mathrm{Fin}\,p\times\mathrm{Fin}\,p)\oplus\mathrm{Fin}\,p\oplus\{*\}\simeq\mathrm{Fin}(p^2+p+1)$ chosen by cardinality, and `heckeGen1RepsAt`, `heckeGen2RepsAt` are the two families at `dig = digit v`, re-indexed along it by $\mathrm{Fin}(N(v)^2+N(v)+1)$.
--
--   The auxiliary material proves these are complete systems of left coset representatives. Over a ring $R$ with fraction field $K$, `integralGL3` is the image of $GL_3(R)$ in $GL_3(K)$; `IsLocalUniformizer ϖ` asserts that $\varpi$ is nonzero, a non-unit, and divides every non-unit; `IsResidueSystem ϖ ℓ` asserts that $\ell$ hits every residue class mod $\varpi$ exactly once. With $\pi\in K^\times$ the image of $\varpi$, `gen1Reps` multiplies unipotents with entries $\ell(\cdot)$ by the slot diagonals $\mathrm{diag}(\pi,1,1)$, $\mathrm{diag}(1,\pi,1)$, $\mathrm{diag}(1,1,\pi)$, and `gen2Reps` is its image under the involution $g\mapsto w_0\,{}^{t}g^{-1}w_0$ times the central unit $\pi$; these are shown to be Hecke coset systems for $\mathrm{diag}(\pi,1,1)$ and $\mathrm{diag}(\pi,\pi,1)$ by Hermite reduction of integral matrices. Transport lemmas (central translation, conjugation, involutive or injective homomorphisms, re-indexing along a bijection, and completeness from equal cardinality), a bridge identifying `integralGL3` over the valuation ring with `localMaximalCompact3` and the slot diagonals with `heckeGen1 v`, `heckeGen2 v`, the residue system $\mathcal{O}_{\mathbb{Q}}/v$ with chosen lifts, and valuation computations for integer casts (in particular that distinct naturals below $N(v)$ differ by a unit) complete the package.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Hecke coset system or of explicit double-coset representatives for $GL_3$ over a local field; those are the project's own. `integralGL3` is the range of Mathlib's `Matrix.GeneralLinearGroup.map` along `algebraMap R K`, and `IsLocalUniformizer`, `IsResidueSystem` are elementary divisibility predicates used in place of Mathlib's discrete valuation ring API.
--
--   **Where it is used.** The families defined here are the representative sets against which the local Hecke eigenvalue conditions at the two generators `heckeGen1 v`, `heckeGen2 v` of the spherical Hecke algebra of $GL_3(\mathbb{Q}_v)$ are tested, in the form of `IsCosetEigenfunction` inside `IsInducedSphericalAt`. They thus serve the cubic induction step, which produces the automorphic form on $GL_3$ attached to a cubic-field induced datum in the Langlands–Tunnell input to modularity of the mod $3$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_HeckeRepresentatives.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives

noncomputable def digit (v : HeightOneSpectrum (𝓞 ℚ)) (d : Fin (Ideal.absNorm v.asIdeal)) : v.adicCompletion ℚ :=
  ((d : ℕ) : v.adicCompletion ℚ)

noncomputable def heckeGen1Reps (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) :
    (α × α) ⊕ α ⊕ Unit → LocalGL3 v :=
  Sum.elim (fun ab => upperUnipotent3 (dig ab.1) 0 (dig ab.2) * twoRowPointLocal v 1 0)
    (Sum.elim (fun c => upperUnipotent3 0 (dig c) 0 * twoRowPointLocal v 0 1)
      fun _ => centralGen v * (heckeGen2 v)⁻¹)

noncomputable def heckeGen2Reps (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) :
    (α × α) ⊕ α ⊕ Unit → LocalGL3 v :=
  Sum.elim (fun bc => upperUnipotent3 0 (dig bc.2) (dig bc.1) * twoRowPointLocal v 1 1)
    (Sum.elim (fun a => upperUnipotent3 (dig a) 0 0 * (twoRowPointLocal v 1 0 * (centralGen v * (heckeGen2 v)⁻¹)))
      fun _ => twoRowPointLocal v 0 1 * (centralGen v * (heckeGen2 v)⁻¹))

theorem heckeGen1Reps_inl (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (ab : α × α) :
    heckeGen1Reps v dig (Sum.inl ab) = upperUnipotent3 (dig ab.1) 0 (dig ab.2) * twoRowPointLocal v 1 0 :=
  rfl

theorem heckeGen1Reps_inr_inl (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (c : α) :
    heckeGen1Reps v dig (Sum.inr (Sum.inl c)) = upperUnipotent3 0 (dig c) 0 * twoRowPointLocal v 0 1 :=
  rfl

theorem heckeGen1Reps_inr_inr (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (u : Unit) :
    heckeGen1Reps v dig (Sum.inr (Sum.inr u)) = centralGen v * (heckeGen2 v)⁻¹ :=
  rfl

theorem heckeGen2Reps_inl (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (bc : α × α) :
    heckeGen2Reps v dig (Sum.inl bc) = upperUnipotent3 0 (dig bc.2) (dig bc.1) * twoRowPointLocal v 1 1 :=
  rfl

theorem heckeGen2Reps_inr_inl (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (a : α) :
    heckeGen2Reps v dig (Sum.inr (Sum.inl a)) =
      upperUnipotent3 (dig a) 0 0 * (twoRowPointLocal v 1 0 * (centralGen v * (heckeGen2 v)⁻¹)) :=
  rfl

theorem heckeGen2Reps_inr_inr (v : HeightOneSpectrum (𝓞 ℚ)) {α : Type} (dig : α → v.adicCompletion ℚ) (u : Unit) :
    heckeGen2Reps v dig (Sum.inr (Sum.inr u)) = twoRowPointLocal v 0 1 * (centralGen v * (heckeGen2 v)⁻¹) :=
  rfl

noncomputable def repIndexEquiv (p : ℕ) : (Fin p × Fin p) ⊕ Fin p ⊕ Unit ≃ Fin (p ^ 2 + p + 1) :=
  Fintype.equivFinOfCardEq
    (by simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]; ring)

noncomputable def heckeGen1RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v :=
  heckeGen1Reps v (digit v) ∘ (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

noncomputable def heckeGen2RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v :=
  heckeGen2Reps v (digit v) ∘ (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

end LanglandsTunnell.CubicInduction.HeckeRepresentatives

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite

section Transport

open HeckeIntegralSeam HeckePair

variable {G H : Type*} [Group G] [Group H]

private theorem inv_mul_mul_central_eq {z : G} (hz : ∀ x : G, z * x = x * z) (a b : G) :
    (a * z)⁻¹ * (b * z) = a⁻¹ * b := by
  have hzi : ∀ x : G, z⁻¹ * x = x * z⁻¹ := fun x => (Commute.inv_left (hz x : Commute z x)).eq
  rw [_root_.mul_inv_rev, mul_assoc, hzi]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

private theorem isHeckeCosetSystem_mul_central (U : Subgroup G) (g z : G) (hz : ∀ x : G, z * x = x * z)
    {ι : Type*} {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) :
    IsHeckeCosetSystem U (g * z) fun i => reps i * z where
  mem_doubleCoset i := by
    obtain ⟨u, hu, w, hw, hrep⟩ := mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    refine mem_doubleCoset_iff.mpr ⟨u, hu, w, hw, ?_⟩
    rw [← mul_assoc, mul_assoc (u * g) z w, hz w, ← mul_assoc, hrep]
  covers x hx := by
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
    have hx' : u * g * w ∈ doubleCoset U g := mem_doubleCoset_iff.mpr ⟨u, hu, w, hw, rfl⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hx'
    refine ⟨i, ?_⟩
    have hform : u * (g * z) * w = u * g * w * z := by
      rw [← mul_assoc, mul_assoc (u * g) z w, hz w, ← mul_assoc]
    show (QuotientGroup.mk (u * (g * z) * w) : G ⧸ U) = QuotientGroup.mk (reps i * z)
    rw [hform]
    refine QuotientGroup.eq.mpr ?_
    rw [inv_mul_mul_central_eq hz]
    exact QuotientGroup.eq.mp hi
  mk_injective := by
    intro i j hij
    have hij' : (QuotientGroup.mk (reps i * z) : G ⧸ U) = QuotientGroup.mk (reps j * z) := hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    refine QuotientGroup.eq.mpr ?_
    have h1 := QuotientGroup.eq.mp hij'
    rw [inv_mul_mul_central_eq hz] at h1
    exact h1

private theorem isHeckeCosetSystem_conj (U : Subgroup G) (g : G) {k : G} (hk : k ∈ U)
    {ι : Type*} {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) :
    IsHeckeCosetSystem U g fun i => k⁻¹ * reps i * k where
  mem_doubleCoset i := by
    obtain ⟨u, hu, w, hw, hrep⟩ := mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    refine mem_doubleCoset_iff.mpr ⟨k⁻¹ * u, U.mul_mem (U.inv_mem hk) hu, w * k, U.mul_mem hw hk, ?_⟩
    rw [← hrep]
    simp only [mul_assoc]
  covers x hx := by
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
    have hx' : (k * u) * g * (w * k⁻¹) ∈ doubleCoset U g :=
      mem_doubleCoset_iff.mpr ⟨k * u, U.mul_mem hk hu, w * k⁻¹, U.mul_mem hw (U.inv_mem hk), rfl⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hx'
    refine ⟨i, ?_⟩
    have h1 : ((k * u) * g * (w * k⁻¹))⁻¹ * reps i ∈ U := QuotientGroup.eq.mp hi
    show (QuotientGroup.mk (u * g * w) : G ⧸ U) = QuotientGroup.mk (k⁻¹ * reps i * k)
    refine QuotientGroup.eq.mpr ?_
    have h2 : (u * g * w)⁻¹ * (k⁻¹ * reps i * k) = k⁻¹ * (((k * u) * g * (w * k⁻¹))⁻¹ * reps i) * k := by
      simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [h2]
    exact U.mul_mem (U.mul_mem (U.inv_mem hk) h1) hk
  mk_injective := by
    intro i j hij
    have hij' : (QuotientGroup.mk (k⁻¹ * reps i * k) : G ⧸ U) = QuotientGroup.mk (k⁻¹ * reps j * k) := hij
    have h1 : (k⁻¹ * reps i * k)⁻¹ * (k⁻¹ * reps j * k) ∈ U := QuotientGroup.eq.mp hij'
    have h2 : (reps i)⁻¹ * reps j = k * ((k⁻¹ * reps i * k)⁻¹ * (k⁻¹ * reps j * k)) * k⁻¹ := by
      simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    refine QuotientGroup.eq.mpr ?_
    rw [h2]
    exact U.mul_mem (U.mul_mem hk h1) (U.inv_mem hk)

private theorem isHeckeCosetSystem_map_of_involutive (U : Subgroup G) (g : G) (θ : G →* G)
    (hθθ : ∀ x, θ (θ x) = x) (hθU : ∀ x, x ∈ U → θ x ∈ U)
    {ι : Type*} {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) :
    IsHeckeCosetSystem U (θ g) fun i => θ (reps i) where
  mem_doubleCoset i := by
    obtain ⟨u, hu, w, hw, hrep⟩ := mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact mem_doubleCoset_iff.mpr ⟨θ u, hθU u hu, θ w, hθU w hw, by rw [← map_mul, ← map_mul, hrep]⟩
  covers x hx := by
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
    have hx' : θ u * g * θ w ∈ doubleCoset U g :=
      mem_doubleCoset_iff.mpr ⟨θ u, hθU u hu, θ w, hθU w hw, rfl⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hx'
    refine ⟨i, ?_⟩
    show (QuotientGroup.mk (u * θ g * w) : G ⧸ U) = QuotientGroup.mk (θ (reps i))
    refine QuotientGroup.eq.mpr ?_
    have h1 := hθU _ (QuotientGroup.eq.mp hi)
    rw [map_mul, map_inv, map_mul, map_mul, hθθ, hθθ] at h1
    exact h1
  mk_injective := by
    intro i j hij
    have hij' : (QuotientGroup.mk (θ (reps i)) : G ⧸ U) = QuotientGroup.mk (θ (reps j)) := hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    refine QuotientGroup.eq.mpr ?_
    have h1 := hθU _ (QuotientGroup.eq.mp hij')
    rw [map_mul, map_inv, hθθ, hθθ] at h1
    exact h1

private theorem isHeckeCosetSystem_map_of_injective (U : Subgroup G) (g : G) (φ : G →* H)
    (hφ : Function.Injective φ) {ι : Type*} {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) :
    IsHeckeCosetSystem (U.map φ) (φ g) fun i => φ (reps i) where
  mem_doubleCoset i := by
    obtain ⟨u, hu, w, hw, hrep⟩ := mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact mem_doubleCoset_iff.mpr ⟨φ u, Subgroup.mem_map_of_mem φ hu, φ w, Subgroup.mem_map_of_mem φ hw,
      by rw [← map_mul, ← map_mul, hrep]⟩
  covers x hx := by
    obtain ⟨u', hu', w', hw', rfl⟩ := mem_doubleCoset_iff.mp hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'
    have hx' : u * g * w ∈ doubleCoset U g := mem_doubleCoset_iff.mpr ⟨u, hu, w, hw, rfl⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hx'
    refine ⟨i, ?_⟩
    show (QuotientGroup.mk (φ u * φ g * φ w) : H ⧸ U.map φ) = QuotientGroup.mk (φ (reps i))
    refine QuotientGroup.eq.mpr ?_
    have h1 := QuotientGroup.eq.mp hi
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem φ h1
  mk_injective := by
    intro i j hij
    have hij' : (QuotientGroup.mk (φ (reps i)) : H ⧸ U.map φ) = QuotientGroup.mk (φ (reps j)) := hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    refine QuotientGroup.eq.mpr ?_
    have h1 := QuotientGroup.eq.mp hij'
    rw [← map_inv, ← map_mul] at h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
    rw [hφ hyx] at hy
    exact hy

end Transport

section ExplicitMatrices

variable {A : Type*} [CommRing A]

private noncomputable def diagUnits3 (a b c : Aˣ) : GL (Fin 3) A where
  val := Matrix.diagonal ![(a : A), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A), ((c⁻¹ : Aˣ) : A)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[simp] private theorem diagUnits3_coe (a b c : Aˣ) :
    (diagUnits3 a b c : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal ![(a : A), b, c] := rfl

@[simp] private theorem diagUnits3_inv_coe (a b c : Aˣ) :
    ((diagUnits3 a b c)⁻¹ : GL (Fin 3) A).val
      = Matrix.diagonal ![((a⁻¹ : Aˣ) : A), ((b⁻¹ : Aˣ) : A), ((c⁻¹ : Aˣ) : A)] := rfl

private noncomputable def centralUnit3 (u : Aˣ) : GL (Fin 3) A := diagUnits3 u u u

private theorem centralUnit3_comm (u : Aˣ) (x : GL (Fin 3) A) : centralUnit3 u * x = x * centralUnit3 u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.diagonal ![(u : A), u, u] * (x : Matrix (Fin 3) (Fin 3) A)
    = (x : Matrix (Fin 3) (Fin 3) A) * Matrix.diagonal ![(u : A), u, u]
  have h : (![(u : A), u, u] : Fin 3 → A) = fun _ => (u : A) := by
    ext i; fin_cases i <;> rfl
  rw [h, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

private noncomputable def slotDiag (π : Aˣ) : Fin 3 → GL (Fin 3) A := ![diagUnits3 π 1 1, diagUnits3 1 π 1,
    diagUnits3 1 1 π]

private noncomputable def slotDiag2 (π : Aˣ) : Fin 3 → GL (Fin 3) A := ![diagUnits3 π π 1, diagUnits3 π 1 π,
    diagUnits3 1 π π]

private theorem diagUnits3_mul (a b c a' b' c' : Aˣ) :
    diagUnits3 a b c * diagUnits3 a' b' c' = diagUnits3 (a * a') (b * b') (c * c') := by
  apply Units.ext
  rw [Units.val_mul, diagUnits3_coe, diagUnits3_coe, diagUnits3_coe, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

private noncomputable def longWeyl3 : GL (Fin 3) A where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] private theorem longWeyl3_coe :
    (longWeyl3 : GL (Fin 3) A).val = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

private theorem longWeyl3_inv : (longWeyl3 : GL (Fin 3) A)⁻¹ = longWeyl3 := Units.ext rfl

private theorem longWeyl3_mul_self : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  rw [← longWeyl3_inv]
  exact mul_inv_cancel _

private theorem longWeyl3_coe_transpose :
    ((longWeyl3 : GL (Fin 3) A).val)ᵀ = (longWeyl3 : GL (Fin 3) A).val := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private noncomputable def swap01 : GL (Fin 3) A where
  val := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  inv := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[simp] private theorem swap01_coe : (swap01 : GL (Fin 3) A).val = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl

private theorem swap01_inv : (swap01 : GL (Fin 3) A)⁻¹ = swap01 := Units.ext rfl

private noncomputable def invTranspose3 : GL (Fin 3) A →* GL (Fin 3) A where
  toFun x :=
    { val := (x.inv)ᵀ
      inv := (x.val)ᵀ
      val_inv := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext (by
    show ((1 : Matrix (Fin 3) (Fin 3) A))ᵀ = (1 : Matrix (Fin 3) (Fin 3) A)
    exact Matrix.transpose_one)
  map_mul' x y := Units.ext (by
    show ((x * y).inv)ᵀ = (x.inv)ᵀ * (y.inv)ᵀ
    show (y.inv * x.inv)ᵀ = (x.inv)ᵀ * (y.inv)ᵀ
    rw [Matrix.transpose_mul])

@[simp] private theorem invTranspose3_coe (x : GL (Fin 3) A) :
    (invTranspose3 x : GL (Fin 3) A).val = ((x⁻¹ : GL (Fin 3) A).val)ᵀ := rfl

private theorem invTranspose3_invTranspose3 (x : GL (Fin 3) A) : invTranspose3 (invTranspose3 x) = x :=
  Units.ext (by
    show ((invTranspose3 x).inv)ᵀ = x.val
    show ((x.val)ᵀ)ᵀ = x.val
    rw [Matrix.transpose_transpose])

private noncomputable def theta3 : GL (Fin 3) A →* GL (Fin 3) A :=
  (MulAut.conj (longWeyl3 : GL (Fin 3) A)).toMonoidHom.comp invTranspose3

private theorem theta3_apply (x : GL (Fin 3) A) :
    theta3 x = longWeyl3 * invTranspose3 x * longWeyl3 := by
  show longWeyl3 * invTranspose3 x * longWeyl3⁻¹ = _
  rw [longWeyl3_inv]

private theorem invTranspose3_longWeyl3 : invTranspose3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 :=
  Units.ext (by
    show ((longWeyl3 : GL (Fin 3) A).inv)ᵀ = (longWeyl3 : GL (Fin 3) A).val
    exact longWeyl3_coe_transpose)

private theorem theta3_theta3 (x : GL (Fin 3) A) : theta3 (theta3 x) = x := by
  rw [theta3_apply, theta3_apply, map_mul, map_mul, invTranspose3_longWeyl3, invTranspose3_invTranspose3]
  calc longWeyl3 * (longWeyl3 * x * longWeyl3) * longWeyl3
      = (longWeyl3 * longWeyl3) * x * (longWeyl3 * longWeyl3) := by simp only [mul_assoc]
    _ = x := by rw [longWeyl3_mul_self, one_mul, mul_one]

private theorem diagUnits3_coe_fin (a b c : Aˣ) :
    (diagUnits3 a b c : GL (Fin 3) A).val = !![(a : A), 0, 0; 0, (b : A), 0; 0, 0, (c : A)] := by
  rw [diagUnits3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem swap01_mul_diagUnits3_mul_swap01 (a b c : Aˣ) :
    swap01 * diagUnits3 a b c * swap01 = diagUnits3 b a c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, swap01_coe, diagUnits3_coe_fin, diagUnits3_coe_fin, Matrix.mul_fin_three,
    Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem longWeyl3_mul_diagUnits3_mul_longWeyl3 (a b c : Aˣ) :
    longWeyl3 * diagUnits3 a b c * longWeyl3 = diagUnits3 c b a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, diagUnits3_coe_fin, diagUnits3_coe_fin, Matrix.mul_fin_three,
    Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem invTranspose3_diagUnits3 (a b c : Aˣ) :
    invTranspose3 (diagUnits3 a b c) = diagUnits3 a⁻¹ b⁻¹ c⁻¹ := by
  apply Units.ext
  rw [invTranspose3_coe, diagUnits3_inv_coe, Matrix.diagonal_transpose, diagUnits3_coe]

private theorem theta3_diagUnits3 (a b c : Aˣ) : theta3 (diagUnits3 a b c) = diagUnits3 c⁻¹ b⁻¹ a⁻¹ := by
  rw [theta3_apply, invTranspose3_diagUnits3, longWeyl3_mul_diagUnits3_mul_longWeyl3]

end ExplicitMatrices

section DiagonalConjugation

open LanglandsTunnell.CubicInduction

variable {A : Type*} [CommRing A]

private theorem diagUnits3_mul_upperUnipotent3 (a b c : Aˣ) (x y z : A) :
    diagUnits3 a b c * upperUnipotent3 x y z
      = upperUnipotent3 ((a : A) * x * ((b⁻¹ : Aˣ) : A)) ((b : A) * y * ((c⁻¹ : Aˣ) : A))
          ((a : A) * z * ((c⁻¹ : Aˣ) : A)) * diagUnits3 a b c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diagUnits3_coe_fin, upperUnipotent3_coe, upperUnipotent3_coe,
    Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end DiagonalConjugation

section DiagonalContinuity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in

private theorem continuous_diagUnits3 :
    Continuous fun t : Aˣ × Aˣ × Aˣ => (diagUnits3 t.1 t.2.1 t.2.2 : GL (Fin 3) A) := by
  have h1 : Continuous fun t : Aˣ × Aˣ × Aˣ => (t.1 : A) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun t : Aˣ × Aˣ × Aˣ => (t.2.1 : A) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  have h3 : Continuous fun t : Aˣ × Aˣ × Aˣ => (t.2.2 : A) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_snd)
  have h1' : Continuous fun t : Aˣ × Aˣ × Aˣ => ((t.1⁻¹ : Aˣ) : A) :=
    Units.continuous_coe_inv.comp continuous_fst
  have h2' : Continuous fun t : Aˣ × Aˣ × Aˣ => ((t.2.1⁻¹ : Aˣ) : A) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  have h3' : Continuous fun t : Aˣ × Aˣ × Aˣ => ((t.2.2⁻¹ : Aˣ) : A) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun t : Aˣ × Aˣ × Aˣ => (![(t.1 : A), t.2.1, t.2.2] : Fin 3 → A) :=
    continuous_pi fun i => by
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
  have hv' : Continuous fun t : Aˣ × Aˣ × Aˣ =>
      (![((t.1⁻¹ : Aˣ) : A), ((t.2.1⁻¹ : Aˣ) : A), ((t.2.2⁻¹ : Aˣ) : A)] : Fin 3 → A) :=
    continuous_pi fun i => by
      fin_cases i
      · exact h1'
      · exact h2'
      · exact h3'
  exact Units.continuous_iff.2 ⟨hv.matrix_diagonal, hv'.matrix_diagonal⟩

end DiagonalContinuity

section Integral

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private noncomputable def integralGL3 (R K : Type*) [CommRing R] [Field K] [Algebra R K] : Subgroup (GL (Fin 3) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 3) (algebraMap R K)).range

private theorem mem_integralGL3_iff {z : GL (Fin 3) K} :
    z ∈ integralGL3 R K ↔ ∃ y : GL (Fin 3) R, Matrix.GeneralLinearGroup.map (algebraMap R K) y = z :=
  Iff.rfl

private theorem mem_integralGL3_of_coe_eq (z : GL (Fin 3) K) (M : Matrix (Fin 3) (Fin 3) R) (hM : IsUnit M.det)
    (h : (z : Matrix (Fin 3) (Fin 3) K) = M.map (algebraMap R K)) : z ∈ integralGL3 R K :=
  mem_integralGL3_iff.mpr ⟨Matrix.nonsingInvUnit (A := M) hM, Units.ext h.symm⟩

private theorem map_mem_integralGL3 (y : GL (Fin 3) R) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) y ∈ integralGL3 R K :=
  mem_integralGL3_iff.mpr ⟨y, rfl⟩

private theorem exists_coe_eq_of_mem_integralGL3 {z : GL (Fin 3) K} (hz : z ∈ integralGL3 R K) (i j : Fin 3) :
    ∃ r : R, algebraMap R K r = (z : Matrix (Fin 3) (Fin 3) K) i j := by
  obtain ⟨y, rfl⟩ := mem_integralGL3_iff.mp hz
  exact ⟨(y : Matrix (Fin 3) (Fin 3) R) i j, (Matrix.GeneralLinearGroup.map_apply _ i j y).symm⟩

private theorem map_longWeyl3 :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (longWeyl3 : GL (Fin 3) R) = longWeyl3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply]

private theorem map_swap01 :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (swap01 : GL (Fin 3) R) = swap01 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply]

private theorem map_upperUnipotent3 (x y z : R) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (LanglandsTunnell.CubicInduction.upperUnipotent3 x y z)
      = LanglandsTunnell.CubicInduction.upperUnipotent3 (algebraMap R K x) (algebraMap R K y)
          (algebraMap R K z) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, LanglandsTunnell.CubicInduction.upperUnipotent3]

private theorem map_invTranspose3 (y : GL (Fin 3) R) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (invTranspose3 y)
      = invTranspose3 (Matrix.GeneralLinearGroup.map (algebraMap R K) y) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, invTranspose3_coe, Matrix.transpose_apply]
  rw [← Matrix.GeneralLinearGroup.map_inv]
  exact (Matrix.GeneralLinearGroup.map_apply _ j i y⁻¹).symm

private theorem map_theta3 (y : GL (Fin 3) R) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (theta3 y)
      = theta3 (Matrix.GeneralLinearGroup.map (algebraMap R K) y) := by
  rw [theta3_apply, theta3_apply, map_mul, map_mul, map_longWeyl3, map_invTranspose3]

private theorem theta3_mem_integralGL3 {x : GL (Fin 3) K} (hx : x ∈ integralGL3 R K) :
    theta3 x ∈ integralGL3 R K := by
  obtain ⟨y, rfl⟩ := mem_integralGL3_iff.mp hx
  rw [← map_theta3]
  exact map_mem_integralGL3 _

private theorem longWeyl3_mem_integralGL3 : (longWeyl3 : GL (Fin 3) K) ∈ integralGL3 R K := by
  rw [← map_longWeyl3 (R := R)]
  exact map_mem_integralGL3 _

private theorem swap01_mem_integralGL3 : (swap01 : GL (Fin 3) K) ∈ integralGL3 R K := by
  rw [← map_swap01 (R := R)]
  exact map_mem_integralGL3 _

private theorem upperUnipotent3_mem_integralGL3 (x y z : R) :
    LanglandsTunnell.CubicInduction.upperUnipotent3 (algebraMap R K x) (algebraMap R K y) (algebraMap R K z)
      ∈ integralGL3 R K := by
  rw [← map_upperUnipotent3]
  exact map_mem_integralGL3 _

variable (hinj : Function.Injective (algebraMap R K))
include hinj

private theorem algebraMap_ne_zero_of_ne_zero {ϖ : R} (hϖ0 : ϖ ≠ 0) : algebraMap R K ϖ ≠ 0 := by
  intro h0
  exact hϖ0 (hinj (by rw [h0, map_zero]))

private theorem false_of_algebraMap_eq_inv {ϖ : R} (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (r : R)
    (h : algebraMap R K r = (algebraMap R K ϖ)⁻¹) : False := by
  apply hϖ
  have h1 : ϖ * r = 1 := hinj (by
    rw [map_mul, map_one, h, mul_inv_cancel₀ (algebraMap_ne_zero_of_ne_zero hinj hϖ0)])
  exact ⟨⟨ϖ, r, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

private theorem dvd_sub_of_algebraMap_eq_inv_mul {ϖ : R} (hϖ0 : ϖ ≠ 0) (r s t : R)
    (h : algebraMap R K r = (algebraMap R K ϖ)⁻¹ * (algebraMap R K s - algebraMap R K t)) :
    ϖ ∣ s - t := by
  refine ⟨r, hinj ?_⟩
  rw [map_sub, map_mul, h, mul_inv_cancel_left₀ (algebraMap_ne_zero_of_ne_zero hinj hϖ0)]

end Integral

section Gen1

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private structure IsLocalUniformizer (ϖ : R) : Prop where
  ne_zero : ϖ ≠ 0
  not_isUnit : ¬ IsUnit ϖ
  dvd_of_not_isUnit : ∀ r : R, ¬ IsUnit r → ϖ ∣ r

private structure IsResidueSystem (ϖ : R) {κ : Type} (ℓ : κ → R) : Prop where
  exists_dvd_sub : ∀ r : R, ∃ c : κ, ϖ ∣ r - ℓ c
  eq_of_dvd_sub : ∀ c c' : κ, ϖ ∣ ℓ c - ℓ c' → c = c'

private theorem upperUnipotent3_inv_coe {A : Type*} [CommRing A] (x y z : A) :
    ((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A).val = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl

private noncomputable abbrev Gen1Index (κ : Type) : Type := (κ × κ) ⊕ (κ ⊕ Unit)

private noncomputable def slotOf {κ : Type} : Gen1Index κ → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private noncomputable def gen1Unip {κ : Type} (ℓ : κ → R) : Gen1Index κ → GL (Fin 3) K
  | Sum.inl (a, b) => upperUnipotent3 (algebraMap R K (ℓ a)) 0 (algebraMap R K (ℓ b))
  | Sum.inr (Sum.inl c) => upperUnipotent3 0 (algebraMap R K (ℓ c)) 0
  | Sum.inr (Sum.inr _) => upperUnipotent3 0 0 0

private noncomputable def gen1Reps (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) : GL (Fin 3) K :=
  gen1Unip ℓ i * slotDiag π (slotOf i)

private theorem gen1Reps_eq_unip_mul (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) :
    gen1Reps π ℓ i = gen1Unip ℓ i * slotDiag π (slotOf i) := rfl

variable (π : Kˣ) {κ : Type} (ℓ : κ → R)

private theorem gen1Reps_inl_coe (a b : κ) :
    (gen1Reps π ℓ (Sum.inl (a, b)) : Matrix (Fin 3) (Fin 3) K)
      = !![(π : K), algebraMap R K (ℓ a), algebraMap R K (ℓ b); 0, 1, 0; 0, 0, 1] := by
  show (upperUnipotent3 (algebraMap R K (ℓ a)) 0 (algebraMap R K (ℓ b)) * diagUnits3 π 1 1 : GL (Fin 3) K).val = _
  rw [Units.val_mul, upperUnipotent3_coe, diagUnits3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal]

private theorem gen1Reps_inr_inl_coe (c : κ) :
    (gen1Reps π ℓ (Sum.inr (Sum.inl c)) : Matrix (Fin 3) (Fin 3) K)
      = !![1, 0, 0; 0, (π : K), algebraMap R K (ℓ c); 0, 0, 1] := by
  show (upperUnipotent3 0 (algebraMap R K (ℓ c)) 0 * diagUnits3 1 π 1 : GL (Fin 3) K).val = _
  rw [Units.val_mul, upperUnipotent3_coe, diagUnits3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal]

private theorem gen1Reps_inr_inr_coe (u : Unit) :
    (gen1Reps π ℓ (Sum.inr (Sum.inr u)) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; 0, 0, (π : K)] := by
  show (upperUnipotent3 0 0 0 * diagUnits3 1 1 π : GL (Fin 3) K).val = _
  rw [Units.val_mul, upperUnipotent3_coe, diagUnits3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal]

private theorem gen1Reps_inl_inv_coe (a b : κ) :
    ((gen1Reps π ℓ (Sum.inl (a, b)))⁻¹ : GL (Fin 3) K).val
      = !![((π : K))⁻¹, -(((π : K))⁻¹ * algebraMap R K (ℓ a)), -(((π : K))⁻¹ * algebraMap R K (ℓ b));
          0, 1, 0; 0, 0, 1] := by
  show ((upperUnipotent3 (algebraMap R K (ℓ a)) 0 (algebraMap R K (ℓ b)) * diagUnits3 π 1 1 : GL (Fin 3) K)⁻¹).val
    = _
  rw [_root_.mul_inv_rev, Units.val_mul, upperUnipotent3_inv_coe, diagUnits3_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul]

private theorem gen1Reps_inr_inl_inv_coe (c : κ) :
    ((gen1Reps π ℓ (Sum.inr (Sum.inl c)))⁻¹ : GL (Fin 3) K).val
      = !![1, 0, 0; 0, ((π : K))⁻¹, -(((π : K))⁻¹ * algebraMap R K (ℓ c)); 0, 0, 1] := by
  show ((upperUnipotent3 0 (algebraMap R K (ℓ c)) 0 * diagUnits3 1 π 1 : GL (Fin 3) K)⁻¹).val = _
  rw [_root_.mul_inv_rev, Units.val_mul, upperUnipotent3_inv_coe, diagUnits3_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul]

private theorem gen1Reps_inr_inr_inv_coe (u : Unit) :
    ((gen1Reps π ℓ (Sum.inr (Sum.inr u)))⁻¹ : GL (Fin 3) K).val = !![1, 0, 0; 0, 1, 0; 0, 0, ((π : K))⁻¹] := by
  show ((upperUnipotent3 0 0 0 * diagUnits3 1 1 π : GL (Fin 3) K)⁻¹).val = _
  rw [_root_.mul_inv_rev, Units.val_mul, upperUnipotent3_inv_coe, diagUnits3_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul]

private theorem det_slotDiag_zero : ((slotDiag π 0 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (π : K) := by
  simp [slotDiag, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem det_gen1Reps (i : Gen1Index κ) :
    ((gen1Reps π ℓ i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (π : K) := by
  rcases i with ⟨a, b⟩ | c | u
  · rw [gen1Reps_inl_coe, Matrix.det_fin_three]; simp
  · rw [gen1Reps_inr_inl_coe, Matrix.det_fin_three]; simp
  · rw [gen1Reps_inr_inr_coe, Matrix.det_fin_three]; simp

private theorem slotDiag_one_eq_conj : (slotDiag π 1 : GL (Fin 3) K) = swap01 * slotDiag π 0 * swap01 := by
  show diagUnits3 1 π 1 = swap01 * diagUnits3 π 1 1 * swap01
  rw [swap01_mul_diagUnits3_mul_swap01]

private theorem slotDiag_two_eq_conj : (slotDiag π 2 : GL (Fin 3) K) = longWeyl3 * slotDiag π 0 * longWeyl3 := by
  show diagUnits3 1 1 π = longWeyl3 * diagUnits3 π 1 1 * longWeyl3
  rw [longWeyl3_mul_diagUnits3_mul_longWeyl3]

private theorem gen1Unip_mem (i : Gen1Index κ) : (gen1Unip ℓ i : GL (Fin 3) K) ∈ integralGL3 R K := by
  rcases i with ⟨a, b⟩ | c | u
  · have h := upperUnipotent3_mem_integralGL3 (K := K) (ℓ a) 0 (ℓ b)
    rw [map_zero] at h
    exact h
  · have h := upperUnipotent3_mem_integralGL3 (K := K) 0 (ℓ c) 0
    rw [map_zero] at h
    exact h
  · have h := upperUnipotent3_mem_integralGL3 (R := R) (K := K) 0 0 0
    rw [map_zero] at h
    exact h

private theorem gen1Reps_mem_doubleCoset (i : Gen1Index κ) :
    gen1Reps π ℓ i ∈ doubleCoset (integralGL3 R K) (slotDiag π 0) := by
  rw [gen1Reps_eq_unip_mul]
  rcases i with ⟨a, b⟩ | c | u
  · exact mem_doubleCoset_iff.mpr ⟨_, gen1Unip_mem ℓ (Sum.inl (a, b)), 1, one_mem _, by simp [slotOf]⟩
  · refine mem_doubleCoset_iff.mpr ⟨gen1Unip ℓ (Sum.inr (Sum.inl c)) * swap01,
      mul_mem (gen1Unip_mem ℓ _) swap01_mem_integralGL3, swap01, swap01_mem_integralGL3, ?_⟩
    show _ = gen1Unip ℓ (Sum.inr (Sum.inl c)) * slotDiag π 1
    rw [slotDiag_one_eq_conj]
    simp only [mul_assoc]
  · refine mem_doubleCoset_iff.mpr ⟨gen1Unip ℓ (Sum.inr (Sum.inr u)) * longWeyl3,
      mul_mem (gen1Unip_mem ℓ _) longWeyl3_mem_integralGL3, longWeyl3, longWeyl3_mem_integralGL3, ?_⟩
    show _ = gen1Unip ℓ (Sum.inr (Sum.inr u)) * slotDiag π 2
    rw [slotDiag_two_eq_conj]
    simp only [mul_assoc]

private theorem det_map_algebraMap (M : Matrix (Fin 3) (Fin 3) R) :
    (M.map (algebraMap R K)).det = algebraMap R K M.det :=
  (RingHom.map_det (algebraMap R K) M).symm

private theorem coe_map_algebraMap (y : GL (Fin 3) R) :
    (Matrix.GeneralLinearGroup.map (algebraMap R K) y : Matrix (Fin 3) (Fin 3) K)
      = (y : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) := rfl

variable {π ℓ}

private theorem inv_mul_mul_mem_integralGL3 (hinj : Function.Injective (algebraMap R K)) (y : GL (Fin 3) R)
    (ξ : GL (Fin 3) K) (hξ : (ξ : Matrix (Fin 3) (Fin 3) K).det = (π : K)) (M : Matrix (Fin 3) (Fin 3) R)
    (E : (slotDiag π 0 : Matrix (Fin 3) (Fin 3) K) * M.map (algebraMap R K)
      = (y : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) * (ξ : Matrix (Fin 3) (Fin 3) K)) :
    (slotDiag π 0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) y * ξ ∈ integralGL3 R K := by
  have hdet : IsUnit M.det := by
    have h1 := congrArg Matrix.det E
    rw [Matrix.det_mul, Matrix.det_mul, det_slotDiag_zero, hξ, det_map_algebraMap, det_map_algebraMap] at h1
    have h2 : M.det = (y : Matrix (Fin 3) (Fin 3) R).det :=
      hinj (mul_left_cancel₀ π.ne_zero (h1.trans (mul_comm _ _)))
    rw [h2]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit y)
  refine mem_integralGL3_of_coe_eq _ M hdet ?_
  rw [Units.val_mul, Units.val_mul, coe_map_algebraMap, mul_assoc, ← E, ← mul_assoc, Units.inv_mul, one_mul]

section Cases

variable {ϖ : R}

private theorem exists_residue_unit_mul_add (hres : IsResidueSystem ϖ ℓ) (e : Rˣ) (s : R) :
    ∃ (c : κ) (q : R), (e : R) * ℓ c + s = ϖ * q := by
  obtain ⟨c, t, ht⟩ := hres.exists_dvd_sub (-(((e⁻¹ : Rˣ) : R) * s))
  refine ⟨c, -((e : R) * t), ?_⟩
  have hee : (e : R) * ((e⁻¹ : Rˣ) : R) = 1 := e.mul_inv
  linear_combination (-(e : R)) * ht + (-s) * hee

private theorem exists_mem_of_isUnit_fst (hinj : Function.Injective (algebraMap R K)) (hπ : (π : K) = algebraMap R K ϖ)
    (hres : IsResidueSystem ϖ ℓ) (y : GL (Fin 3) R) (hu : IsUnit ((y : Matrix (Fin 3) (Fin 3) R) 0 0)) :
    ∃ i : Gen1Index κ,
      (slotDiag π 0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) y * gen1Reps π ℓ i ∈ integralGL3 R K := by
  obtain ⟨e, he⟩ := hu
  obtain ⟨a, qa, hqa⟩ := exists_residue_unit_mul_add hres e ((y : Matrix (Fin 3) (Fin 3) R) 0 1)
  obtain ⟨b, qb, hqb⟩ := exists_residue_unit_mul_add hres e ((y : Matrix (Fin 3) (Fin 3) R) 0 2)
  rw [he] at hqa hqb
  have hqa' : algebraMap R K ϖ * algebraMap R K qa
      = algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 0) * algebraMap R K (ℓ a)
        + algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 1) := by
    rw [← map_mul, ← hqa, map_add, map_mul]
  have hqb' : algebraMap R K ϖ * algebraMap R K qb
      = algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 0) * algebraMap R K (ℓ b)
        + algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 2) := by
    rw [← map_mul, ← hqb, map_add, map_mul]
  refine ⟨Sum.inl (a, b), inv_mul_mul_mem_integralGL3 hinj y _ (det_gen1Reps π ℓ _)
    !![(y : Matrix (Fin 3) (Fin 3) R) 0 0, qa, qb;
       (y : Matrix (Fin 3) (Fin 3) R) 1 0 * ϖ,
         (y : Matrix (Fin 3) (Fin 3) R) 1 0 * ℓ a + (y : Matrix (Fin 3) (Fin 3) R) 1 1,
         (y : Matrix (Fin 3) (Fin 3) R) 1 0 * ℓ b + (y : Matrix (Fin 3) (Fin 3) R) 1 2;
       (y : Matrix (Fin 3) (Fin 3) R) 2 0 * ϖ,
         (y : Matrix (Fin 3) (Fin 3) R) 2 0 * ℓ a + (y : Matrix (Fin 3) (Fin 3) R) 2 1,
         (y : Matrix (Fin 3) (Fin 3) R) 2 0 * ℓ b + (y : Matrix (Fin 3) (Fin 3) R) 2 2] ?_⟩
  rw [gen1Reps_inl_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slotDiag, Matrix.mul_apply, Fin.sum_univ_three, hπ] <;>
    first
      | ring1
      | linear_combination hqa'
      | linear_combination hqb'

private theorem exists_mem_of_dvd_fst_of_isUnit_snd (hinj : Function.Injective (algebraMap R K))
    (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) (y : GL (Fin 3) R)
    (h0 : ϖ ∣ (y : Matrix (Fin 3) (Fin 3) R) 0 0) (hu : IsUnit ((y : Matrix (Fin 3) (Fin 3) R) 0 1)) :
    ∃ i : Gen1Index κ,
      (slotDiag π 0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) y * gen1Reps π ℓ i ∈ integralGL3 R K := by
  obtain ⟨p₀, hp₀⟩ := h0
  obtain ⟨e, he⟩ := hu
  obtain ⟨c, q, hq⟩ := exists_residue_unit_mul_add hres e ((y : Matrix (Fin 3) (Fin 3) R) 0 2)
  rw [he] at hq
  have hp₀' : algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 0) = algebraMap R K ϖ * algebraMap R K p₀ := by
    rw [← map_mul, ← hp₀]
  have hq' : algebraMap R K ϖ * algebraMap R K q
      = algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 1) * algebraMap R K (ℓ c)
        + algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 2) := by
    rw [← map_mul, ← hq, map_add, map_mul]
  refine ⟨Sum.inr (Sum.inl c), inv_mul_mul_mem_integralGL3 hinj y _ (det_gen1Reps π ℓ _)
    !![p₀, (y : Matrix (Fin 3) (Fin 3) R) 0 1, q;
       (y : Matrix (Fin 3) (Fin 3) R) 1 0, (y : Matrix (Fin 3) (Fin 3) R) 1 1 * ϖ,
         (y : Matrix (Fin 3) (Fin 3) R) 1 1 * ℓ c + (y : Matrix (Fin 3) (Fin 3) R) 1 2;
       (y : Matrix (Fin 3) (Fin 3) R) 2 0, (y : Matrix (Fin 3) (Fin 3) R) 2 1 * ϖ,
         (y : Matrix (Fin 3) (Fin 3) R) 2 1 * ℓ c + (y : Matrix (Fin 3) (Fin 3) R) 2 2] ?_⟩
  rw [gen1Reps_inr_inl_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slotDiag, Matrix.mul_apply, Fin.sum_univ_three, hπ] <;>
    first
      | ring1
      | linear_combination (-1 : K) * hp₀'
      | linear_combination hq'

private theorem exists_mem_of_dvd_fst_of_dvd_snd (hinj : Function.Injective (algebraMap R K))
    (hπ : (π : K) = algebraMap R K ϖ) (y : GL (Fin 3) R) (h0 : ϖ ∣ (y : Matrix (Fin 3) (Fin 3) R) 0 0)
    (h1 : ϖ ∣ (y : Matrix (Fin 3) (Fin 3) R) 0 1) :
    ∃ i : Gen1Index κ,
      (slotDiag π 0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) y * gen1Reps π ℓ i ∈ integralGL3 R K := by
  obtain ⟨p₀, hp₀⟩ := h0
  obtain ⟨p₁, hp₁⟩ := h1
  have hp₀' : algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 0) = algebraMap R K ϖ * algebraMap R K p₀ := by
    rw [← map_mul, ← hp₀]
  have hp₁' : algebraMap R K ((y : Matrix (Fin 3) (Fin 3) R) 0 1) = algebraMap R K ϖ * algebraMap R K p₁ := by
    rw [← map_mul, ← hp₁]
  refine ⟨Sum.inr (Sum.inr ()), inv_mul_mul_mem_integralGL3 hinj y _ (det_gen1Reps π ℓ _)
    !![p₀, p₁, (y : Matrix (Fin 3) (Fin 3) R) 0 2;
       (y : Matrix (Fin 3) (Fin 3) R) 1 0, (y : Matrix (Fin 3) (Fin 3) R) 1 1,
         (y : Matrix (Fin 3) (Fin 3) R) 1 2 * ϖ;
       (y : Matrix (Fin 3) (Fin 3) R) 2 0, (y : Matrix (Fin 3) (Fin 3) R) 2 1,
         (y : Matrix (Fin 3) (Fin 3) R) 2 2 * ϖ] ?_⟩
  rw [gen1Reps_inr_inr_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slotDiag, Matrix.mul_apply, Fin.sum_univ_three, hπ] <;>
    first
      | ring1
      | linear_combination (-1 : K) * hp₀'
      | linear_combination (-1 : K) * hp₁'

end Cases

private theorem gen1_covers (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) (x : GL (Fin 3) K)
    (hx : x ∈ doubleCoset (integralGL3 R K) (slotDiag π 0)) :
    ∃ i : Gen1Index κ,
      (QuotientGroup.mk x : GL (Fin 3) K ⧸ integralGL3 R K) = QuotientGroup.mk (gen1Reps π ℓ i) := by
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset_iff.mp hx
  obtain ⟨y₀, rfl⟩ := mem_integralGL3_iff.mp hu
  have key : ∃ i : Gen1Index κ, (slotDiag π 0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) y₀⁻¹
      * gen1Reps π ℓ i ∈ integralGL3 R K := by
    by_cases h00 : IsUnit (((y₀⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0)
    · exact exists_mem_of_isUnit_fst hinj hπ hres _ h00
    · by_cases h01 : IsUnit (((y₀⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 1)
      · exact exists_mem_of_dvd_fst_of_isUnit_snd hinj hπ hres _ (hϖ.dvd_of_not_isUnit _ h00) h01
      · exact exists_mem_of_dvd_fst_of_dvd_snd hinj hπ _ (hϖ.dvd_of_not_isUnit _ h00)
          (hϖ.dvd_of_not_isUnit _ h01)
  obtain ⟨i, hi⟩ := key
  refine ⟨i, ?_⟩
  rw [QuotientGroup.mk_mul_of_mem _ hw]
  refine QuotientGroup.eq.mpr ?_
  rw [_root_.mul_inv_rev, ← map_inv]
  exact hi

section Disjoint

private theorem eq_of_inl_inl (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) (a b a' b' : κ)
    (h : (gen1Reps π ℓ (Sum.inl (a, b)))⁻¹ * gen1Reps π ℓ (Sum.inl (a', b')) ∈ integralGL3 R K) :
    a = a' ∧ b = b' := by
  obtain ⟨r₁, hr₁⟩ := exists_coe_eq_of_mem_integralGL3 h 0 1
  obtain ⟨r₂, hr₂⟩ := exists_coe_eq_of_mem_integralGL3 h 0 2
  rw [Units.val_mul, gen1Reps_inl_inv_coe, gen1Reps_inl_coe] at hr₁ hr₂
  simp [Matrix.mul_apply, Fin.sum_univ_three, hπ] at hr₁ hr₂
  constructor
  · exact (hres.eq_of_dvd_sub a' a
      (dvd_sub_of_algebraMap_eq_inv_mul hinj hϖ.ne_zero r₁ (ℓ a') (ℓ a) (hr₁.trans (by ring1)))).symm
  · exact (hres.eq_of_dvd_sub b' b
      (dvd_sub_of_algebraMap_eq_inv_mul hinj hϖ.ne_zero r₂ (ℓ b') (ℓ b) (hr₂.trans (by ring1)))).symm

private theorem eq_of_inr_inl_inr_inl (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) (c c' : κ)
    (h : (gen1Reps π ℓ (Sum.inr (Sum.inl c)))⁻¹ * gen1Reps π ℓ (Sum.inr (Sum.inl c')) ∈ integralGL3 R K) :
    c = c' := by
  obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 h 1 2
  rw [Units.val_mul, gen1Reps_inr_inl_inv_coe, gen1Reps_inr_inl_coe] at hr
  simp [Matrix.mul_apply, Fin.sum_univ_three, hπ] at hr
  exact (hres.eq_of_dvd_sub c' c
    (dvd_sub_of_algebraMap_eq_inv_mul hinj hϖ.ne_zero r (ℓ c') (ℓ c) (hr.trans (by ring1)))).symm

private theorem not_inl_inr_inl (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (a b c : κ)
    (h : (gen1Reps π ℓ (Sum.inl (a, b)))⁻¹ * gen1Reps π ℓ (Sum.inr (Sum.inl c)) ∈ integralGL3 R K) : False := by
  obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 h 0 0
  rw [Units.val_mul, gen1Reps_inl_inv_coe, gen1Reps_inr_inl_coe] at hr
  simp [Matrix.mul_apply, Fin.sum_univ_three, hπ] at hr
  exact false_of_algebraMap_eq_inv hinj hϖ.ne_zero hϖ.not_isUnit r (hr.trans (by ring1))

private theorem not_inl_inr_inr (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (a b : κ) (u : Unit)
    (h : (gen1Reps π ℓ (Sum.inl (a, b)))⁻¹ * gen1Reps π ℓ (Sum.inr (Sum.inr u)) ∈ integralGL3 R K) : False := by
  obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 h 0 0
  rw [Units.val_mul, gen1Reps_inl_inv_coe, gen1Reps_inr_inr_coe] at hr
  simp [Matrix.mul_apply, Fin.sum_univ_three, hπ] at hr
  exact false_of_algebraMap_eq_inv hinj hϖ.ne_zero hϖ.not_isUnit r (hr.trans (by ring1))

private theorem not_inr_inl_inr_inr (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (c : κ) (u : Unit)
    (h : (gen1Reps π ℓ (Sum.inr (Sum.inl c)))⁻¹ * gen1Reps π ℓ (Sum.inr (Sum.inr u)) ∈ integralGL3 R K) :
    False := by
  obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 h 1 1
  rw [Units.val_mul, gen1Reps_inr_inl_inv_coe, gen1Reps_inr_inr_coe] at hr
  simp [Matrix.mul_apply, Fin.sum_univ_three, hπ] at hr
  exact false_of_algebraMap_eq_inv hinj hϖ.ne_zero hϖ.not_isUnit r (hr.trans (by ring1))

end Disjoint

private theorem gen1_mk_injective (hinj : Function.Injective (algebraMap R K)) {ϖ : R} (hϖ : IsLocalUniformizer ϖ)
    (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) :
    Function.Injective fun i : Gen1Index κ =>
      (QuotientGroup.mk (gen1Reps π ℓ i) : GL (Fin 3) K ⧸ integralGL3 R K) := by
  intro i j hij
  have hij' : (QuotientGroup.mk (gen1Reps π ℓ i) : GL (Fin 3) K ⧸ integralGL3 R K)
      = QuotientGroup.mk (gen1Reps π ℓ j) := hij
  have hmem := QuotientGroup.eq.mp hij'
  have hmem' := QuotientGroup.eq.mp hij'.symm
  rcases i with ⟨a, b⟩ | c | u <;> rcases j with ⟨a', b'⟩ | c' | u'
  · obtain ⟨rfl, rfl⟩ := eq_of_inl_inl hinj hϖ hπ hres a b a' b' hmem
    rfl
  · exact (not_inl_inr_inl hinj hϖ hπ a b c' hmem).elim
  · exact (not_inl_inr_inr hinj hϖ hπ a b u' hmem).elim
  · exact (not_inl_inr_inl hinj hϖ hπ a' b' c hmem').elim
  · rw [eq_of_inr_inl_inr_inl hinj hϖ hπ hres c c' hmem]
  · exact (not_inr_inl_inr_inr hinj hϖ hπ c u' hmem).elim
  · exact (not_inl_inr_inr hinj hϖ hπ a' b' u hmem').elim
  · exact (not_inr_inl_inr_inr hinj hϖ hπ c' u hmem').elim
  · cases u
    cases u'
    rfl

private theorem isHeckeCosetSystem_gen1Reps (hinj : Function.Injective (algebraMap R K)) {ϖ : R}
    (hϖ : IsLocalUniformizer ϖ) (hπ : (π : K) = algebraMap R K ϖ) (hres : IsResidueSystem ϖ ℓ) :
    IsHeckeCosetSystem (integralGL3 R K) (slotDiag π 0) (gen1Reps π ℓ) where
  mem_doubleCoset := gen1Reps_mem_doubleCoset π ℓ
  covers := gen1_covers hinj hϖ hπ hres
  mk_injective := gen1_mk_injective hinj hϖ hπ hres

end Gen1

section Gen2

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private theorem theta3_upperUnipotent3 {A : Type*} [CommRing A] (x y z : A) :
    theta3 (upperUnipotent3 x y z) = upperUnipotent3 (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta3_apply, Units.val_mul, Units.val_mul, invTranspose3_coe, upperUnipotent3_inv_coe, longWeyl3_coe,
    upperUnipotent3_coe]
  have ht : (!![(1 : A), -x, x * y - z; 0, 1, -y; 0, 0, 1])ᵀ = !![(1 : A), 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht, Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem theta3_slotDiag_mul_central (π : Kˣ) (s : Fin 3) :
    theta3 (slotDiag π s) * centralUnit3 π = slotDiag2 π s := by
  fin_cases s
  · show theta3 (diagUnits3 π 1 1) * centralUnit3 π = diagUnits3 π π 1
    rw [theta3_diagUnits3, centralUnit3, diagUnits3_mul]
    simp
  · show theta3 (diagUnits3 1 π 1) * centralUnit3 π = diagUnits3 π 1 π
    rw [theta3_diagUnits3, centralUnit3, diagUnits3_mul]
    simp
  · show theta3 (diagUnits3 1 1 π) * centralUnit3 π = diagUnits3 1 π π
    rw [theta3_diagUnits3, centralUnit3, diagUnits3_mul]
    simp

private noncomputable def gen2Reps (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) : GL (Fin 3) K :=
  theta3 (gen1Reps π ℓ i) * centralUnit3 π

private theorem gen2Reps_eq_theta3_unip_mul (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) :
    gen2Reps π ℓ i = theta3 (gen1Unip ℓ i) * slotDiag2 π (slotOf i) := by
  show theta3 (gen1Reps π ℓ i) * centralUnit3 π = _
  rw [gen1Reps_eq_unip_mul, map_mul, mul_assoc, theta3_slotDiag_mul_central]

private theorem isHeckeCosetSystem_gen2Reps (hinj : Function.Injective (algebraMap R K)) {ϖ : R}
    (hϖ : IsLocalUniformizer ϖ) {π : Kˣ} (hπ : (π : K) = algebraMap R K ϖ) {κ : Type} {ℓ : κ → R}
    (hres : IsResidueSystem ϖ ℓ) :
    IsHeckeCosetSystem (integralGL3 R K) (slotDiag2 π 0) (gen2Reps π ℓ) := by
  have h1 := isHeckeCosetSystem_map_of_involutive (integralGL3 R K) (slotDiag π 0) theta3 theta3_theta3
    (fun _ hx => theta3_mem_integralGL3 hx) (isHeckeCosetSystem_gen1Reps hinj hϖ hπ hres)
  have h2 := isHeckeCosetSystem_mul_central (integralGL3 R K) (theta3 (slotDiag π 0)) (centralUnit3 π)
    (centralUnit3_comm π) h1
  rw [theta3_slotDiag_mul_central] at h2
  exact h2

private theorem exists_gen1Unip_eq {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) :
    ∃ x y z : K, (gen1Unip ℓ i : GL (Fin 3) K) = upperUnipotent3 x y z := by
  rcases i with ⟨a, b⟩ | c | u
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

private theorem exists_gen1Reps_eq (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) :
    ∃ x y z : K, gen1Reps π ℓ i = upperUnipotent3 x y z * slotDiag π (slotOf i) := by
  obtain ⟨x, y, z, h⟩ := exists_gen1Unip_eq (K := K) ℓ i
  exact ⟨x, y, z, by rw [gen1Reps_eq_unip_mul, h]⟩

private theorem exists_gen2Reps_eq (π : Kˣ) {κ : Type} (ℓ : κ → R) (i : Gen1Index κ) :
    ∃ x y z : K, gen2Reps π ℓ i = upperUnipotent3 x y z * slotDiag2 π (slotOf i) := by
  obtain ⟨x, y, z, h⟩ := exists_gen1Unip_eq (K := K) ℓ i
  exact ⟨-y, -x, x * y - z, by rw [gen2Reps_eq_theta3_unip_mul, h, theta3_upperUnipotent3]⟩

private theorem slotOf_inl {κ : Type} (ab : κ × κ) : slotOf (Sum.inl ab : Gen1Index κ) = 0 := rfl
private theorem slotOf_inr_inl {κ : Type} (c : κ) : slotOf (Sum.inr (Sum.inl c) : Gen1Index κ) = 1 := rfl
private theorem slotOf_inr_inr {κ : Type} (u : Unit) : slotOf (Sum.inr (Sum.inr u) : Gen1Index κ) = 2 := rfl

private theorem sum_gen1Index {κ : Type} [Fintype κ] {M : Type*} [AddCommMonoid M] (g : Gen1Index κ → M) :
    ∑ i, g i = ∑ ab : κ × κ, g (Sum.inl ab) + (∑ c : κ, g (Sum.inr (Sum.inl c)) + g (Sum.inr (Sum.inr ()))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, PUnit.default_eq_unit]

end Gen2

section Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem lt_one_le_exp_neg_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  · have hlog : WithZero.log a < 0 := (WithZero.log_lt_iff_lt_exp ha).mpr (by simpa using h)
    exact WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (by omega))

private noncomputable def uniformizerInt : v.adicCompletionIntegers ℚ :=
  ⟨varpi v, by
    show Valued.v (varpi v) ≤ 1
    have h : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v
    rw [h]
    exact (WithZero.exp_le_exp (a := (-1 : ℤ)) (b := 0)).mpr (by norm_num)⟩

private theorem valued_uniformizerInt : Valued.v (uniformizerInt v).1 = WithZero.exp (-1 : ℤ) :=
  valued_uniformizerUnit ℚ v

private theorem uniformizerUnit_coe_eq_algebraMap :
    ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)
      = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (uniformizerInt v) := rfl

private theorem isLocalUniformizer_uniformizerInt : IsLocalUniformizer (uniformizerInt v) where
  ne_zero := by
    intro h0
    have h1 := valued_uniformizerInt v
    rw [h0] at h1
    simp only [ZeroMemClass.coe_zero, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  not_isUnit := by
    intro hu
    have h1 := adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
    rw [valued_uniformizerInt] at h1
    have h2 : (-1 : ℤ) = 0 := WithZero.exp_eq_one.mp h1
    norm_num at h2
  dvd_of_not_isUnit := by
    intro r hr
    refine (adicCompletionIntegers.integers ℚ v).dvd_of_le ?_
    show Valued.v r.1 ≤ Valued.v (uniformizerInt v).1
    rw [valued_uniformizerInt]
    refine lt_one_le_exp_neg_one (lt_of_le_of_ne r.2 ?_)
    exact fun h => hr (adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr h)

private theorem integralGL3_eq_localMaximalCompact3 :
    integralGL3 (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) = localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  ext x
  rw [mem_localMaximalCompact3_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ integralGL3 (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) := inv_mem hx
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 hx i j
      rw [← hr]
      exact r.2
    · obtain ⟨r, hr⟩ := exists_coe_eq_of_mem_integralGL3 hx' i j
      rw [← hr]
      exact r.2
  · rintro ⟨h1, h2⟩
    let Y : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers ℚ) :=
      Matrix.of fun i j => ⟨(x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j,
        h1 i j⟩
    let Y' : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers ℚ) :=
      Matrix.of fun i j =>
        ⟨((x⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j,
        h2 i j⟩
    have hY : Y.map (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
        = (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
      ext i j
      rfl
    have hY' : Y'.map (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
        = ((x⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
      ext i j
      rfl
    have hYY' : Y.det * Y'.det = 1 := by
      apply FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      rw [map_mul, map_one, ← det_map_algebraMap, ← det_map_algebraMap, hY, hY', ← Matrix.det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have hdet : IsUnit Y.det := ⟨⟨Y.det, Y'.det, hYY', by rw [mul_comm]; exact hYY'⟩, rfl⟩
    exact mem_integralGL3_of_coe_eq x Y hdet hY.symm

private theorem slotDiag_uniformizerUnit_zero : slotDiag (uniformizerUnit ℚ v) 0 = heckeGen1 v := by
  apply Units.ext
  show Matrix.diagonal ![((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
      ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)]
    = Matrix.diagonal ![varpi v, 1, 1]
  simp

private theorem slotDiag2_uniformizerUnit_zero : slotDiag2 (uniformizerUnit ℚ v) 0 = heckeGen2 v := by
  apply Units.ext
  show Matrix.diagonal ![((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
      ((uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
      ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)]
    = Matrix.diagonal ![varpi v, varpi v, 1]
  simp

end Bridge

section Residues

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicHaar
open NumberField.AdelicLevel LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def ResidueIndex : Type := 𝓞 ℚ ⧸ v.asIdeal

private noncomputable instance finite_residueIndex : Finite (ResidueIndex v) :=
  Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

private noncomputable instance fintype_residueIndex : Fintype (ResidueIndex v) := Fintype.ofFinite _

private noncomputable def residueRep (c : ResidueIndex v) : v.adicCompletionIntegers ℚ :=
  algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) (Quotient.out c)

private theorem residue_algebraMap_eq_zero_iff (a : 𝓞 ℚ) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a) = 0
      ↔ a ∈ v.asIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valued_lt_one]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_lt_one_iff_mem v a

private theorem residue_algebraMap_eq_of_mk_eq {a b : 𝓞 ℚ}
    (h : Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a)
      = IsLocalRing.residue (v.adicCompletionIntegers ℚ) (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) b) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  exact (residue_algebraMap_eq_zero_iff v _).mpr (Ideal.Quotient.eq.mp h)

private theorem residue_residueRep (c : ResidueIndex v) (a : 𝓞 ℚ) (ha : Ideal.Quotient.mk v.asIdeal a = c) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (residueRep v c)
      = IsLocalRing.residue (v.adicCompletionIntegers ℚ) (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a) :=
  residue_algebraMap_eq_of_mk_eq v ((Ideal.Quotient.mk_out c).trans ha.symm)

private theorem not_isUnit_sub_of_residue_eq {x y : v.adicCompletionIntegers ℚ}
    (h : IsLocalRing.residue (v.adicCompletionIntegers ℚ) x = IsLocalRing.residue (v.adicCompletionIntegers ℚ) y) :
    ¬ IsUnit (x - y) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]

private theorem residue_eq_of_not_isUnit_sub {x y : v.adicCompletionIntegers ℚ} (h : ¬ IsUnit (x - y)) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) x = IsLocalRing.residue (v.adicCompletionIntegers ℚ) y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact h

private theorem isResidueSystem_residueRep : IsResidueSystem (uniformizerInt v) (residueRep v) where
  exists_dvd_sub := by
    intro x
    obtain ⟨a, ha⟩ :=
      residue_algebraMap_surjective (𝓞 ℚ) ℚ v (IsLocalRing.residue (v.adicCompletionIntegers ℚ) x)
    refine ⟨Ideal.Quotient.mk v.asIdeal a, (isLocalUniformizer_uniformizerInt v).dvd_of_not_isUnit _ ?_⟩
    refine not_isUnit_sub_of_residue_eq v ?_
    rw [residue_residueRep v _ a rfl]
    exact ha.symm
  eq_of_dvd_sub := by
    intro c c' h
    have hnu : ¬ IsUnit (residueRep v c - residueRep v c') :=
      fun hu => (isLocalUniformizer_uniformizerInt v).not_isUnit (isUnit_of_dvd_unit h hu)
    have hres := residue_eq_of_not_isUnit_sub v hnu
    rw [residue_residueRep v c _ (Ideal.Quotient.mk_out c),
      residue_residueRep v c' _ (Ideal.Quotient.mk_out c')] at hres
    rw [← Ideal.Quotient.mk_out c, ← Ideal.Quotient.mk_out c']
    refine Ideal.Quotient.eq.mpr ((residue_algebraMap_eq_zero_iff v _).mp ?_)
    rw [map_sub, map_sub, hres, sub_self]

private theorem card_residueIndex : Fintype.card (ResidueIndex v) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

private theorem card_residueIndex_prod :
    Fintype.card (ResidueIndex v × ResidueIndex v) = Ideal.absNorm v.asIdeal ^ 2 := by
  rw [Fintype.card_prod, card_residueIndex, sq]

private theorem cNormQ_eq_card : cNormQ v = (Fintype.card (ResidueIndex v) : ℂ) := by
  rw [card_residueIndex]
  rfl

end Residues

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Counting

open HeckeIntegralSeam

variable {G : Type*} [Group G]

private theorem isHeckeCosetSystem_of_card_eq {U : Subgroup G} {g : G} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {reps : ι → G} (hsys : IsHeckeCosetSystem U g reps) {reps' : κ → G}
    (hmem : ∀ j, reps' j ∈ HeckePair.doubleCoset U g)
    (hinj : Function.Injective fun j => (QuotientGroup.mk (reps' j) : G ⧸ U))
    (hcard : Fintype.card κ = Fintype.card ι) :
    IsHeckeCosetSystem U g reps' where
  mem_doubleCoset := hmem
  mk_injective := hinj
  covers x hx := by
    have hcov : ∀ j, ∃ i, (QuotientGroup.mk (reps' j) : G ⧸ U) = QuotientGroup.mk (reps i) :=
      fun j => hsys.covers _ (hmem j)
    choose f hf using hcov
    have hfinj : Function.Injective f := by
      intro j j' h
      apply hinj
      show (QuotientGroup.mk (reps' j) : G ⧸ U) = QuotientGroup.mk (reps' j')
      rw [hf j, hf j', h]
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
    obtain ⟨i, hi⟩ := hsys.covers x hx
    obtain ⟨j, rfl⟩ := hfbij.2 i
    exact ⟨j, hi.trans (hf j).symm⟩

private theorem isHeckeCosetSystem_comp_equiv {U : Subgroup G} {g : G} {ι κ : Type*} {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset j := hsys.mem_doubleCoset (e j)
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨e.symm i, by rw [Function.comp_apply, Equiv.apply_symm_apply]; exact hi⟩
  mk_injective := by
    intro j j' hjj'
    exact e.injective (hsys.mk_injective hjj')

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Counting

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Valuations

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_intCast (z : ℤ) :
    Valued.v ((z : ℤ) : v.adicCompletion ℚ) = v.intValuation (z : 𝓞 ℚ) := by
  rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) z, ← map_intCast (algebraMap (𝓞 ℚ) ℚ) z]
  exact AdelicLevel.valued_algebraMap v (z : 𝓞 ℚ)

private theorem valued_natCast (n : ℕ) :
    Valued.v ((n : ℕ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap v (n : 𝓞 ℚ)

private theorem valued_natCast_le_one (n : ℕ) : Valued.v ((n : ℕ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [valued_natCast]
  exact intValuation_le_one v _

private theorem absNorm_span_intCast (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast (n : ℤ)

private theorem intValuation_intCast_eq_one {z : ℤ} (hz : z ≠ 0) (hlt : z.natAbs < Ideal.absNorm v.asIdeal) :
    v.intValuation (z : 𝓞 ℚ) = 1 := by
  rw [intValuation_eq_one_iff]
  intro hmem
  have hle : Ideal.span {(z : 𝓞 ℚ)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_span_intCast] at hdvd
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hdvd) (not_le.mpr hlt)

private theorem valued_natCast_sub_natCast {a b : ℕ} (hab : a ≠ b) (ha : a < Ideal.absNorm v.asIdeal)
    (hb : b < Ideal.absNorm v.asIdeal) : Valued.v (((a : ℕ) : v.adicCompletion ℚ) - b) = 1 := by
  have hz : ((a : ℤ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have hlt : ((a : ℤ) - b).natAbs < Ideal.absNorm v.asIdeal := by omega
  have hcast : (((a : ℕ) : v.adicCompletion ℚ) - b) = (((a : ℤ) - b : ℤ) : v.adicCompletion ℚ) := by norm_cast
  rw [hcast, valued_intCast, intValuation_intCast_eq_one v hz hlt]

private theorem intValuation_absNorm :
    v.intValuation (Ideal.absNorm v.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, v.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_ratPrimeAt : Valued.v (ratPrimeAt v) = Valued.v (varpi v) := by
  show Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = _
  rw [valued_natCast, intValuation_absNorm]
  exact (AdelicLevel.valued_uniformizerUnit ℚ v).symm

private theorem valued_varpi_lt_one : Valued.v (varpi v) < 1 := by
  show Valued.v (AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) < 1
  rw [AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

private theorem valued_ratPrimeUnit_lt_one :
    Valued.v ((ratPrimeUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) < 1 := by
  show Valued.v (ratPrimeAt v) < 1
  rw [valued_ratPrimeAt]
  exact valued_varpi_lt_one v

private theorem upperUnipotent3_mem_localMaximalCompact3 {x y z : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    (hy : Valued.v y ≤ 1) (hz : Valued.v z ≤ 1) : upperUnipotent3 x y z ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hxy : Valued.v (x * y - z) ≤ 1 :=
    (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_mul _ x y).le.trans (mul_le_one' hx hy)) hz)
  have hv : ((upperUnipotent3 x y z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, x, z; 0, 1, y; 0, 0, 1] := rfl
  have hi : (((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  rw [mem_localMaximalCompact3_iff, hv, hi]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [hx, hy, hz, hxy]

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Valuations

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {α : Type}

variable {v}

private theorem mem_localMaximalCompact3_of_forall (k : LocalGL3 v)
    (h : ∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  exact ⟨h, h'⟩

variable (v)

private noncomputable def selfInverse (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : M * M = 1) :
    LocalGL3 v :=
  ⟨M, M, hM, hM⟩

@[simp] private theorem coe_selfInverse (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : M * M = 1) :
    ((selfInverse v M hM : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = M := rfl

private theorem selfInverse_mem (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : M * M = 1)
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : selfInverse v M hM ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  mem_localMaximalCompact3_of_forall _ h h

private noncomputable def swap12 : LocalGL3 v :=
  selfInverse v !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private noncomputable def swap13 : LocalGL3 v :=
  selfInverse v !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private noncomputable def swap23 : LocalGL3 v :=
  selfInverse v !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

private theorem swap12_mem : swap12 v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  unfold swap12
  exact selfInverse_mem v _ _ (by intro i j; fin_cases i <;> fin_cases j <;> simp)

private theorem swap13_mem : swap13 v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  unfold swap13
  exact selfInverse_mem v _ _ (by intro i j; fin_cases i <;> fin_cases j <;> simp)

private theorem swap23_mem : swap23 v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  unfold swap23
  exact selfInverse_mem v _ _ (by intro i j; fin_cases i <;> fin_cases j <;> simp)

private noncomputable def diagGL3 (a b c : (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := Matrix.diagonal ![(a : v.adicCompletion ℚ), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), (b⁻¹ : (v.adicCompletion ℚ)ˣ),
    (c⁻¹ : (v.adicCompletion ℚ)ˣ)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

@[simp] private theorem coe_diagGL3 (a b c : (v.adicCompletion ℚ)ˣ) :
    ((diagGL3 v a b c : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a : v.adicCompletion ℚ), b, c] := rfl

private theorem conj_regroup (S A B : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :
    S * A * (B * S) = S * (A * B) * S := by
  simp only [Matrix.mul_assoc]

private theorem swap12_diagonal_swap12 (d : Fin 3 → v.adicCompletion ℚ) :
    ((swap12 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.diagonal d *
        ((swap12 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![d 1, d 0, d 2] := by
  simp only [swap12, coe_selfInverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]

private theorem swap13_diagonal_swap13 (d : Fin 3 → v.adicCompletion ℚ) :
    ((swap13 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.diagonal d *
        ((swap13 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![d 2, d 1, d 0] := by
  simp only [swap13, coe_selfInverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]

private theorem swap23_diagonal_swap23 (d : Fin 3 → v.adicCompletion ℚ) :
    ((swap23 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.diagonal d *
        ((swap23 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![d 0, d 2, d 1] := by
  simp only [swap23, coe_selfInverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]

private theorem diagGL3_mem (a b c : (v.adicCompletion ℚ)ˣ) (ha : Valued.v (a : v.adicCompletion ℚ) = 1)
    (hb : Valued.v (b : v.adicCompletion ℚ) = 1) (hc : Valued.v (c : v.adicCompletion ℚ) = 1) :
    diagGL3 v a b c ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  refine mem_localMaximalCompact3_of_forall _ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [diagGL3, Matrix.diagonal, ha, hb, hc]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [diagGL3, Matrix.diagonal, ha, hb, hc]

private noncomputable def deltaUnit : (v.adicCompletion ℚ)ˣ := ratPrimeUnit v * (AdelicLevel.uniformizerUnit ℚ v)⁻¹

@[simp] private theorem coe_deltaUnit :
    ((deltaUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = ratPrimeAt v * (varpi v)⁻¹ := by
  simp [deltaUnit, ratPrimeUnit, varpi]

private theorem valued_deltaUnit (hP : Valued.v (ratPrimeAt v) = Valued.v (varpi v)) :
    Valued.v ((deltaUnit v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
  rw [coe_deltaUnit, map_mul, map_inv₀, hP]
  exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr (varpi_ne_zero v))

private theorem valued_one_unit : Valued.v (((1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) = 1 := by
  simp

private theorem coe_heckeGen1 :
    ((heckeGen1 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, 1, 1] := rfl

private theorem coe_heckeGen2 :
    ((heckeGen2 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, 1] := rfl

private theorem coe_centralGen :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] := rfl

private theorem twoRowPointLocal_one_zero_eq (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) :
    twoRowPointLocal v 1 0 = heckeGen1 v * diagGL3 v (deltaUnit v) 1 1 := by
  have hϖ := varpi_ne_zero v
  ext1
  rw [Units.val_mul, htRP 1 0, coe_heckeGen1, coe_diagGL3, Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ratPrimeUnit]
  all_goals field_simp

private theorem twoRowPointLocal_zero_one_eq (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) :
    twoRowPointLocal v 0 1 = swap12 v * heckeGen1 v * (diagGL3 v (deltaUnit v) 1 1 * swap12 v) := by
  have hϖ := varpi_ne_zero v
  ext1
  rw [htRP 0 1]
  simp only [Units.val_mul, coe_heckeGen1, coe_diagGL3]
  rw [conj_regroup, Matrix.diagonal_mul_diagonal, swap12_diagonal_swap12]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, ratPrimeUnit]
  all_goals field_simp

private theorem corner_eq_swap13 : centralGen v * (heckeGen2 v)⁻¹ = swap13 v * heckeGen1 v * swap13 v := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  simp only [Units.val_mul, coe_heckeGen1, coe_heckeGen2, coe_centralGen]
  rw [swap13_diagonal_swap13, Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem coe_corner :
    ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 1, 0; 0, 0, varpi v] := by
  rw [corner_eq_swap13, Units.val_mul, Units.val_mul, coe_heckeGen1, swap13_diagonal_swap13]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

private theorem twoRowPointLocal_one_one_eq (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) :
    twoRowPointLocal v 1 1 = heckeGen2 v * diagGL3 v (deltaUnit v) (deltaUnit v) 1 := by
  have hϖ := varpi_ne_zero v
  ext1
  rw [Units.val_mul, htRP 1 1, coe_heckeGen2, coe_diagGL3, Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ratPrimeUnit]
  all_goals field_simp

private theorem twoRowPointLocal_one_zero_mul_corner_eq (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) :
    twoRowPointLocal v 1 0 * (centralGen v * (heckeGen2 v)⁻¹) =
      swap23 v * heckeGen2 v * (diagGL3 v (deltaUnit v) 1 1 * swap23 v) := by
  have hϖ := varpi_ne_zero v
  rw [← mul_assoc, mul_inv_eq_iff_eq_mul]
  ext1
  simp only [Units.val_mul, htRP 1 0, coe_heckeGen2, coe_centralGen, coe_diagGL3]
  rw [conj_regroup, Matrix.diagonal_mul_diagonal, swap23_diagonal_swap23, Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, ratPrimeUnit, hϖ]
  all_goals field_simp

private theorem twoRowPointLocal_zero_one_mul_corner_eq (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) :
    twoRowPointLocal v 0 1 * (centralGen v * (heckeGen2 v)⁻¹) =
      swap13 v * heckeGen2 v * (diagGL3 v 1 (deltaUnit v) 1 * swap13 v) := by
  have hϖ := varpi_ne_zero v
  rw [← mul_assoc, mul_inv_eq_iff_eq_mul]
  ext1
  simp only [Units.val_mul, htRP 0 1, coe_heckeGen2, coe_centralGen, coe_diagGL3]
  rw [conj_regroup, Matrix.diagonal_mul_diagonal, swap13_diagonal_swap13, Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, ratPrimeUnit, hϖ]
  all_goals field_simp

private theorem valued_zero_le : Valued.v (0 : v.adicCompletion ℚ) ≤ 1 := by simp

private theorem heckeGen1Reps_mem_doubleCoset (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) (hn : ∀ x y z : v.adicCompletion ℚ, Valued.v x ≤ 1 → Valued.v y ≤ 1 → Valued.v z ≤ 1 →
      upperUnipotent3 x y z ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hP : Valued.v (ratPrimeAt v) = Valued.v (varpi v)) (dig : α → v.adicCompletion ℚ)
    (hdig : ∀ a, Valued.v (dig a) ≤ 1) (i : (α × α) ⊕ α ⊕ Unit) :
    heckeGen1Reps v dig i ∈ HeckePair.doubleCoset (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) := by
  have hδ := diagGL3_mem v (deltaUnit v) 1 1 (valued_deltaUnit v hP) (valued_one_unit v) (valued_one_unit v)
  rcases i with ⟨a, b⟩ | c | _
  · refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨upperUnipotent3 (dig a) 0 (dig b), hn _ _ _ (hdig a) (valued_zero_le v) (hdig b),
        diagGL3 v (deltaUnit v) 1 1, hδ, ?_⟩
    simp only [heckeGen1Reps, Sum.elim_inl, twoRowPointLocal_one_zero_eq v htRP, mul_assoc]
  · refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨upperUnipotent3 0 (dig c) 0 * swap12 v,
        mul_mem (hn _ _ _ (valued_zero_le v) (hdig c) (valued_zero_le v)) (swap12_mem v),
        diagGL3 v (deltaUnit v) 1 1 * swap12 v, mul_mem hδ (swap12_mem v), ?_⟩
    simp only [heckeGen1Reps, Sum.elim_inl, Sum.elim_inr, twoRowPointLocal_zero_one_eq v htRP, mul_assoc]
  · refine HeckePair.mem_doubleCoset_iff.mpr ⟨swap13 v, swap13_mem v, swap13 v, swap13_mem v, ?_⟩
    simp only [heckeGen1Reps, Sum.elim_inr, corner_eq_swap13]

private theorem heckeGen2Reps_mem_doubleCoset (htRP : ∀ k₁ k₂ : ℕ,
      ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
           0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
           0, 0, 1]) (hn : ∀ x y z : v.adicCompletion ℚ, Valued.v x ≤ 1 → Valued.v y ≤ 1 → Valued.v z ≤ 1 →
      upperUnipotent3 x y z ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hP : Valued.v (ratPrimeAt v) = Valued.v (varpi v)) (dig : α → v.adicCompletion ℚ)
    (hdig : ∀ a, Valued.v (dig a) ≤ 1) (i : (α × α) ⊕ α ⊕ Unit) :
    heckeGen2Reps v dig i ∈ HeckePair.doubleCoset (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) := by
  have h1 := valued_deltaUnit v hP
  have hu := valued_one_unit v
  rcases i with ⟨b, c⟩ | a | _
  · refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨upperUnipotent3 0 (dig c) (dig b), hn _ _ _ (valued_zero_le v) (hdig c) (hdig b),
        diagGL3 v (deltaUnit v) (deltaUnit v) 1, diagGL3_mem v _ _ _ h1 h1 hu, ?_⟩
    simp only [heckeGen2Reps, Sum.elim_inl, twoRowPointLocal_one_one_eq v htRP, mul_assoc]
  · refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨upperUnipotent3 (dig a) 0 0 * swap23 v,
        mul_mem (hn _ _ _ (hdig a) (valued_zero_le v) (valued_zero_le v)) (swap23_mem v),
        diagGL3 v (deltaUnit v) 1 1 * swap23 v, mul_mem (diagGL3_mem v _ _ _ h1 hu hu) (swap23_mem v), ?_⟩
    simp only [heckeGen2Reps, Sum.elim_inl, Sum.elim_inr, twoRowPointLocal_one_zero_mul_corner_eq v htRP,
      mul_assoc]
  · refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨swap13 v, swap13_mem v, diagGL3 v 1 (deltaUnit v) 1 * swap13 v,
        mul_mem (diagGL3_mem v _ _ _ hu h1 hu) (swap13_mem v), ?_⟩
    simp only [heckeGen2Reps, Sum.elim_inr, twoRowPointLocal_zero_one_mul_corner_eq v htRP, mul_assoc]

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity

private noncomputable abbrev Mat3 (v : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)

variable {v : HeightOneSpectrum (𝓞 ℚ)} {α : Type}

private theorem not_eq_mul_of_valued {x c k : v.adicCompletion ℚ} (hx : Valued.v x = 1) (hc : Valued.v c < 1)
    (hk : Valued.v k ≤ 1) (h : x = c * k) : False := by
  have h1 : Valued.v x ≤ Valued.v c := by
    rw [h, Valuation.map_mul]
    exact mul_le_of_le_one_right' hk
  rw [hx] at h1
  exact absurd h1 (not_le.mpr hc)

private theorem not_one_eq_mul_of_valued {c k : v.adicCompletion ℚ} (hc : Valued.v c < 1) (hk : Valued.v k ≤ 1)
    (h : (1 : v.adicCompletion ℚ) = c * k) : False :=
  not_eq_mul_of_valued (Valuation.map_one _) hc hk h

private theorem exists_integral_factor {U : Subgroup (LocalGL3 v)}
    (hU : ∀ k ∈ U, ∀ i j, Valued.v ((k : Mat3 v) i j) ≤ 1)
    {r s : LocalGL3 v}
    (h : (QuotientGroup.mk r : LocalGL3 v ⧸ U) = QuotientGroup.mk s) :
    ∃ k : Mat3 v,
      (∀ i j, Valued.v (k i j) ≤ 1) ∧ (s : Mat3 v) = (r : Mat3 v) * k :=
  ⟨((r⁻¹ * s : LocalGL3 v) : Mat3 v), hU _ (QuotientGroup.eq.mp h), by
    rw [← Units.val_mul, mul_inv_cancel_left]⟩

private theorem coe_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    ((upperUnipotent3 x y z : LocalGL3 v) : Mat3 v) = !![1, x, z; 0, 1, y; 0, 0, 1] :=
  rfl

section Matrices

variable (v)

private theorem coe_twoRowPointLocal' (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Mat3 v) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
         0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
         0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoRowPointLocal, embedMat2, Units.val_pow_eq_pow_val]

variable {v}

private theorem coe_heckeGen1Reps_inl (dig : α → v.adicCompletion ℚ) (ab : α × α) :
    ((heckeGen1Reps v dig (Sum.inl ab) : LocalGL3 v) : Mat3 v) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ), dig ab.1, dig ab.2; 0, 1, 0; 0, 0, 1] := by
  simp only [heckeGen1Reps, Sum.elim_inl, Units.val_mul, coe_upperUnipotent3, coe_twoRowPointLocal']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_heckeGen1Reps_inr_inl (dig : α → v.adicCompletion ℚ) (c : α) :
    ((heckeGen1Reps v dig (Sum.inr (Sum.inl c)) : LocalGL3 v) : Mat3 v) =
      !![1, 0, 0; 0, (ratPrimeUnit v : v.adicCompletion ℚ), dig c; 0, 0, 1] := by
  simp only [heckeGen1Reps, Sum.elim_inr, Sum.elim_inl, Units.val_mul, coe_upperUnipotent3, coe_twoRowPointLocal']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_heckeGen1Reps_inr_inr (dig : α → v.adicCompletion ℚ) {ϖ : v.adicCompletion ℚ}
    (hcorner :
      ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])
    (u : Unit) :
    ((heckeGen1Reps v dig (Sum.inr (Sum.inr u)) : LocalGL3 v) : Mat3 v) =
      !![1, 0, 0; 0, 1, 0; 0, 0, ϖ] := by
  simp only [heckeGen1Reps, Sum.elim_inr]
  exact hcorner

private theorem coe_heckeGen2Reps_inl (dig : α → v.adicCompletion ℚ) (bc : α × α) :
    ((heckeGen2Reps v dig (Sum.inl bc) : LocalGL3 v) : Mat3 v) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ), 0, dig bc.1;
         0, (ratPrimeUnit v : v.adicCompletion ℚ), dig bc.2;
         0, 0, 1] := by
  simp only [heckeGen2Reps, Sum.elim_inl, Units.val_mul, coe_upperUnipotent3, coe_twoRowPointLocal']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_heckeGen2Reps_inr_inl (dig : α → v.adicCompletion ℚ) {ϖ : v.adicCompletion ℚ}
    (hcorner :
      ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])
    (a : α) :
    ((heckeGen2Reps v dig (Sum.inr (Sum.inl a)) : LocalGL3 v) : Mat3 v) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ), dig a, 0; 0, 1, 0; 0, 0, ϖ] := by
  simp only [heckeGen2Reps, Sum.elim_inr, Sum.elim_inl]
  rw [Units.val_mul, Units.val_mul, hcorner, coe_upperUnipotent3, coe_twoRowPointLocal']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_heckeGen2Reps_inr_inr (dig : α → v.adicCompletion ℚ) {ϖ : v.adicCompletion ℚ}
    (hcorner :
      ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])
    (u : Unit) :
    ((heckeGen2Reps v dig (Sum.inr (Sum.inr u)) : LocalGL3 v) : Mat3 v) =
      !![1, 0, 0; 0, (ratPrimeUnit v : v.adicCompletion ℚ), 0; 0, 0, ϖ] := by
  simp only [heckeGen2Reps, Sum.elim_inr]
  rw [Units.val_mul, hcorner, coe_twoRowPointLocal']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Matrices

section Injective

variable {U : Subgroup (LocalGL3 v)}
variable (hU : ∀ k ∈ U, ∀ i j, Valued.v ((k : Mat3 v) i j) ≤ 1)
variable (dig : α → v.adicCompletion ℚ) (hsep : ∀ a b : α, a ≠ b → Valued.v (dig a - dig b) = 1)
variable (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) < 1) {ϖ : v.adicCompletion ℚ} (hϖ : Valued.v ϖ < 1)
variable (hcorner :
  ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])

private theorem entry_of_eq {r s k : Mat3 v} (h : s = r * k)
    (i j : Fin 3) :
    s i j = r i 0 * k 0 j + r i 1 * k 1 j + r i 2 * k 2 j := by
  rw [h, Matrix.mul_apply, Fin.sum_univ_three]

include hU dig hsep hP hϖ hcorner in

private theorem heckeGen1Reps_mk_injective :
    Function.Injective fun i => (QuotientGroup.mk (heckeGen1Reps v dig i) : LocalGL3 v ⧸ U) := by
  intro i j hij
  obtain ⟨k, hk, hsk⟩ := exists_integral_factor hU hij
  rcases i with ⟨a, b⟩ | c | ⟨⟩ <;> rcases j with ⟨a', b'⟩ | c' | ⟨⟩
  · rw [coe_heckeGen1Reps_inl, coe_heckeGen1Reps_inl] at hsk
    have k11 : k 1 1 = 1 := by simpa using (entry_of_eq hsk 1 1).symm
    have k21 : k 2 1 = 0 := by simpa using (entry_of_eq hsk 2 1).symm
    have k12 : k 1 2 = 0 := by simpa using (entry_of_eq hsk 1 2).symm
    have k22 : k 2 2 = 1 := by simpa using (entry_of_eq hsk 2 2).symm
    have ha : a = a' := by
      by_contra hne
      have e := entry_of_eq hsk 0 1
      simp [k11, k21] at e
      exact not_eq_mul_of_valued (hsep a' a (Ne.symm hne)) hP (hk 0 1) (by rw [e]; ring)
    have hb : b = b' := by
      by_contra hne
      have e := entry_of_eq hsk 0 2
      simp [k12, k22] at e
      exact not_eq_mul_of_valued (hsep b' b (Ne.symm hne)) hP (hk 0 2) (by rw [e]; ring)
    rw [ha, hb]
  · exfalso
    rw [coe_heckeGen1Reps_inl, coe_heckeGen1Reps_inr_inl] at hsk
    have k10 : k 1 0 = 0 := by simpa using (entry_of_eq hsk 1 0).symm
    have k20 : k 2 0 = 0 := by simpa using (entry_of_eq hsk 2 0).symm
    have e := entry_of_eq hsk 0 0
    simp [k10, k20] at e
    exact not_one_eq_mul_of_valued hP (hk 0 0) e
  · exfalso
    rw [coe_heckeGen1Reps_inl, coe_heckeGen1Reps_inr_inr dig hcorner] at hsk
    have k10 : k 1 0 = 0 := by simpa using (entry_of_eq hsk 1 0).symm
    have k20 : k 2 0 = 0 := by simpa using (entry_of_eq hsk 2 0).symm
    have e := entry_of_eq hsk 0 0
    simp [k10, k20] at e
    exact not_one_eq_mul_of_valued hP (hk 0 0) e
  · exfalso
    rw [coe_heckeGen1Reps_inr_inl, coe_heckeGen1Reps_inl] at hsk
    have k21 : k 2 1 = 0 := by simpa using (entry_of_eq hsk 2 1).symm
    have e := entry_of_eq hsk 1 1
    simp [k21] at e
    exact not_one_eq_mul_of_valued hP (hk 1 1) e
  · rw [coe_heckeGen1Reps_inr_inl, coe_heckeGen1Reps_inr_inl] at hsk
    have k22 : k 2 2 = 1 := by simpa using (entry_of_eq hsk 2 2).symm
    have hc : c = c' := by
      by_contra hne
      have e := entry_of_eq hsk 1 2
      simp [k22] at e
      exact not_eq_mul_of_valued (hsep c' c (Ne.symm hne)) hP (hk 1 2) (by rw [e]; ring)
    rw [hc]
  · exfalso
    rw [coe_heckeGen1Reps_inr_inl, coe_heckeGen1Reps_inr_inr dig hcorner] at hsk
    have k21 : k 2 1 = 0 := by simpa using (entry_of_eq hsk 2 1).symm
    have e := entry_of_eq hsk 1 1
    simp [k21] at e
    exact not_one_eq_mul_of_valued hP (hk 1 1) e
  · exfalso
    rw [coe_heckeGen1Reps_inr_inr dig hcorner, coe_heckeGen1Reps_inl] at hsk
    have e := entry_of_eq hsk 2 2
    simp at e
    exact not_one_eq_mul_of_valued hϖ (hk 2 2) e
  · exfalso
    rw [coe_heckeGen1Reps_inr_inr dig hcorner, coe_heckeGen1Reps_inr_inl] at hsk
    have e := entry_of_eq hsk 2 2
    simp at e
    exact not_one_eq_mul_of_valued hϖ (hk 2 2) e
  · rfl

include hU dig hsep hP hϖ hcorner in

private theorem heckeGen2Reps_mk_injective :
    Function.Injective fun i => (QuotientGroup.mk (heckeGen2Reps v dig i) : LocalGL3 v ⧸ U) := by
  intro i j hij
  obtain ⟨k, hk, hsk⟩ := exists_integral_factor hU hij
  rcases i with ⟨b, c⟩ | a | ⟨⟩ <;> rcases j with ⟨b', c'⟩ | a' | ⟨⟩
  · rw [coe_heckeGen2Reps_inl, coe_heckeGen2Reps_inl] at hsk
    have k22 : k 2 2 = 1 := by simpa using (entry_of_eq hsk 2 2).symm
    have hb : b = b' := by
      by_contra hne
      have e := entry_of_eq hsk 0 2
      simp [k22] at e
      exact not_eq_mul_of_valued (hsep b' b (Ne.symm hne)) hP (hk 0 2) (by rw [e]; ring)
    have hc : c = c' := by
      by_contra hne
      have e := entry_of_eq hsk 1 2
      simp [k22] at e
      exact not_eq_mul_of_valued (hsep c' c (Ne.symm hne)) hP (hk 1 2) (by rw [e]; ring)
    rw [hb, hc]
  · exfalso
    rw [coe_heckeGen2Reps_inl, coe_heckeGen2Reps_inr_inl dig hcorner] at hsk
    have k21 : k 2 1 = 0 := by simpa using (entry_of_eq hsk 2 1).symm
    have e := entry_of_eq hsk 1 1
    simp [k21] at e
    exact not_one_eq_mul_of_valued hP (hk 1 1) e
  · exfalso
    rw [coe_heckeGen2Reps_inl, coe_heckeGen2Reps_inr_inr dig hcorner] at hsk
    have k20 : k 2 0 = 0 := by simpa using (entry_of_eq hsk 2 0).symm
    have e := entry_of_eq hsk 0 0
    simp [k20] at e
    exact not_one_eq_mul_of_valued hP (hk 0 0) e
  · exfalso
    rw [coe_heckeGen2Reps_inr_inl dig hcorner, coe_heckeGen2Reps_inl] at hsk
    have e := entry_of_eq hsk 2 2
    simp at e
    exact not_one_eq_mul_of_valued hϖ (hk 2 2) e
  · rw [coe_heckeGen2Reps_inr_inl dig hcorner, coe_heckeGen2Reps_inr_inl dig hcorner] at hsk
    have k11 : k 1 1 = 1 := by simpa using (entry_of_eq hsk 1 1).symm
    have ha : a = a' := by
      by_contra hne
      have e := entry_of_eq hsk 0 1
      simp [k11] at e
      exact not_eq_mul_of_valued (hsep a' a (Ne.symm hne)) hP (hk 0 1) (by rw [e]; ring)
    rw [ha]
  · exfalso
    rw [coe_heckeGen2Reps_inr_inl dig hcorner, coe_heckeGen2Reps_inr_inr dig hcorner] at hsk
    have k10 : k 1 0 = 0 := by simpa using (entry_of_eq hsk 1 0).symm
    have e := entry_of_eq hsk 0 0
    simp [k10] at e
    exact not_one_eq_mul_of_valued hP (hk 0 0) e
  · exfalso
    rw [coe_heckeGen2Reps_inr_inr dig hcorner, coe_heckeGen2Reps_inl] at hsk
    have e := entry_of_eq hsk 2 2
    simp at e
    exact not_one_eq_mul_of_valued hϖ (hk 2 2) e
  · exfalso
    rw [coe_heckeGen2Reps_inr_inr dig hcorner, coe_heckeGen2Reps_inr_inl dig hcorner] at hsk
    have e := entry_of_eq hsk 1 1
    simp at e
    exact not_one_eq_mul_of_valued hP (hk 1 1) e
  · rfl

private theorem heckeGen1Reps_mk_injective_localMaximalCompact3 (dig : α → v.adicCompletion ℚ)
    (hsep : ∀ a b : α, a ≠ b → Valued.v (dig a - dig b) = 1) (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) < 1)
    {ϖ : v.adicCompletion ℚ} (hϖ : Valued.v ϖ < 1)
    (hcorner : ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ]) :
    Function.Injective fun i =>
      (QuotientGroup.mk (heckeGen1Reps v dig i) : LocalGL3 v ⧸ localMaximalCompact3 (𝓞 ℚ) ℚ v) :=
  heckeGen1Reps_mk_injective (fun k (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) => hk.1) dig hsep hP hϖ hcorner

private theorem heckeGen2Reps_mk_injective_localMaximalCompact3 (dig : α → v.adicCompletion ℚ)
    (hsep : ∀ a b : α, a ≠ b → Valued.v (dig a - dig b) = 1) (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) < 1)
    {ϖ : v.adicCompletion ℚ} (hϖ : Valued.v ϖ < 1)
    (hcorner : ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ]) :
    Function.Injective fun i =>
      (QuotientGroup.mk (heckeGen2Reps v dig i) : LocalGL3 v ⧸ localMaximalCompact3 (𝓞 ℚ) ℚ v) :=
  heckeGen2Reps_mk_injective (fun k (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) => hk.1) dig hsep hP hϖ hcorner

end Injective

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives

section Systems

open HeckeIntegralSeam NumberField.AdelicLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_twoRowPointLocal (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(ratPrimeUnit v : v.adicCompletion ℚ) ^ k₁, 0, 0;
         0, (ratPrimeUnit v : v.adicCompletion ℚ) ^ k₂, 0;
         0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoRowPointLocal, embedMat2, Units.val_pow_eq_pow_val]

private theorem valued_digit_sub_digit {a b : Fin (Ideal.absNorm v.asIdeal)} (hab : a ≠ b) :
    Valued.v (digit v a - digit v b) = 1 :=
  Valuations.valued_natCast_sub_natCast v (Fin.val_ne_of_ne hab) a.isLt b.isLt

private theorem isHeckeCosetSystem_hermite_heckeGen1 :
    IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v)
      (Hermite.gen1Reps (uniformizerUnit ℚ v) (Hermite.residueRep v)) := by
  have h := Hermite.isHeckeCosetSystem_gen1Reps (π := uniformizerUnit ℚ v)
    (FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
    (Hermite.isLocalUniformizer_uniformizerInt v) (Hermite.uniformizerUnit_coe_eq_algebraMap v)
    (Hermite.isResidueSystem_residueRep v)
  rw [Hermite.integralGL3_eq_localMaximalCompact3, Hermite.slotDiag_uniformizerUnit_zero] at h
  exact h

private theorem isHeckeCosetSystem_hermite_heckeGen2 :
    IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v)
      (Hermite.gen2Reps (uniformizerUnit ℚ v) (Hermite.residueRep v)) := by
  have h := Hermite.isHeckeCosetSystem_gen2Reps (π := uniformizerUnit ℚ v)
    (FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))
    (Hermite.isLocalUniformizer_uniformizerInt v) (Hermite.uniformizerUnit_coe_eq_algebraMap v)
    (Hermite.isResidueSystem_residueRep v)
  rw [Hermite.integralGL3_eq_localMaximalCompact3, Hermite.slotDiag2_uniformizerUnit_zero] at h
  exact h

private theorem card_digitIndex_eq_card_residueIndex :
    Fintype.card (Fin (Ideal.absNorm v.asIdeal) × Fin (Ideal.absNorm v.asIdeal) ⊕
        Fin (Ideal.absNorm v.asIdeal) ⊕ Unit) =
      Fintype.card (Hermite.Gen1Index (Hermite.ResidueIndex v)) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, Hermite.card_residueIndex]

theorem isHeckeCosetSystem_heckeGen1Reps_digit (v : HeightOneSpectrum (𝓞 ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v)
      (heckeGen1Reps v (digit v)) :=
  Counting.isHeckeCosetSystem_of_card_eq (isHeckeCosetSystem_hermite_heckeGen1 v)
    (Membership.heckeGen1Reps_mem_doubleCoset v (coe_twoRowPointLocal v)
      (fun _ _ _ hx hy hz => Valuations.upperUnipotent3_mem_localMaximalCompact3 v hx hy hz)
      (Valuations.valued_ratPrimeAt v) (digit v) (fun d => Valuations.valued_natCast_le_one v d))
    (Injectivity.heckeGen1Reps_mk_injective_localMaximalCompact3 (digit v)
      (fun _ _ hab => valued_digit_sub_digit v hab) (Valuations.valued_ratPrimeUnit_lt_one v)
      (Valuations.valued_varpi_lt_one v) (Membership.coe_corner v))
    (card_digitIndex_eq_card_residueIndex v)

theorem isHeckeCosetSystem_heckeGen2Reps_digit (v : HeightOneSpectrum (𝓞 ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v)
      (heckeGen2Reps v (digit v)) :=
  Counting.isHeckeCosetSystem_of_card_eq (isHeckeCosetSystem_hermite_heckeGen2 v)
    (Membership.heckeGen2Reps_mem_doubleCoset v (coe_twoRowPointLocal v)
      (fun _ _ _ hx hy hz => Valuations.upperUnipotent3_mem_localMaximalCompact3 v hx hy hz)
      (Valuations.valued_ratPrimeAt v) (digit v) (fun d => Valuations.valued_natCast_le_one v d))
    (Injectivity.heckeGen2Reps_mk_injective_localMaximalCompact3 (digit v)
      (fun _ _ hab => valued_digit_sub_digit v hab) (Valuations.valued_ratPrimeUnit_lt_one v)
      (Valuations.valued_varpi_lt_one v) (Membership.coe_corner v))
    (card_digitIndex_eq_card_residueIndex v)

theorem isHeckeCosetSystem_heckeGen1RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) (heckeGen1RepsAt v) :=
  Counting.isHeckeCosetSystem_comp_equiv (isHeckeCosetSystem_heckeGen1Reps_digit v)
    (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

theorem isHeckeCosetSystem_heckeGen2RepsAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) (heckeGen2RepsAt v) :=
  Counting.isHeckeCosetSystem_comp_equiv (isHeckeCosetSystem_heckeGen2Reps_digit v)
    (repIndexEquiv (Ideal.absNorm v.asIdeal)).symm

end Systems

end LanglandsTunnell.CubicInduction.HeckeRepresentatives

end


