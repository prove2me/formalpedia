-- Prove2me | Definitions.Def_mme_tensor_bridge
-- name    : mme_tensor_bridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T17:10:01.210774+00:00
-- url     : https://prove2.me/theorems/9c8d233d-9859-4502-8688-e088ed1c9fdb
-- statement:
--   **Bridge: concrete MME matrix-multiplication tensors $\leftrightarrow$ the abstract asymptotic spectrum.**
--
--   The largest single file in the MME ω<51/20 development. Instantiates the abstract spectral theory of `Def_mme_mm_spectral` on the concrete tensor quotient `TensorQ K 3`, with matrix-multiplication elements $\mathrm{MMq}\,K\,n\,m\,p = \mathrm{toQ}(\mathrm{MMObj}\,K\,n\,m\,p)$, and connects the abstract quantities to the concrete ones occurring in the τ-theorem's goal.
--
--   **`mmTensorData K`.** A bundle of type `MMData (TensorQ K 3) (tensorPreorder K)` packaging the six structural facts that `MMData.sum_inequality` requires: multiplicativity ($\mathrm{MMq}\,K\,n\,m\,p \cdot \mathrm{MMq}\,K\,n'\,m'\,p' \sim_P \mathrm{MMq}\,K\,(nn')(mm')(pp')$ via `MMObj_kron_iso`); monotonicity ($n \leq n' \Rightarrow \mathrm{MMq}\,K\,n\,m\,p \leq_P \mathrm{MMq}\,K\,n'\,m\,p$); trivial bounds ($\mathrm{MMq}\,K\,n\,m\,p \leq_P nmp$); zero ($\mathrm{MMq}\,K\,0\,m\,p = 0$, used in the zero-dim reduction); cyclic symmetry via `permAut cyclicPerm` (`Def_mme_permutation`).
--
--   **The two bridges.**
--   - `bridge_asymptoticRank` — $\mathrm{asymptoticRank}_{\mathrm{tensorPreorder}\,K}\bigl(\sum_i \mathrm{MMq}\,K\,n_i\,m_i\,p_i\bigr) = \mathrm{tensorAsymptoticRank}\bigl(\bigoplus_i \mathrm{MMObj}\,K\,n_i\,m_i\,p_i\bigr)$. The abstract rank on the quotient equals the concrete rank on `TensorObj`; the proof routes through `TensorQ.tensorAsymptoticRank_eq` and `toQ_bigAdd` (`Def_mme_rank_bridge`).
--   - `bridge_omega` — $(\mathrm{mmTensorData}\,K).\omega_{\mathrm{abs}} = \mathrm{matMulExp\_strassen}\,K$. Picks a maximizing spectrum point via compactness, evaluates $\mathrm{MMq}\,K\,2\,2\,2$ via `MM_eval`, applies Strassen duality, and uses the canonical normalization `matMulExp_strassen_eq_log_AR` (`Def_mme_omega_normalize`).
--
--   **Top-level user-facing theorem (proved here).** `mme_sum_inequality` (and its positive form `mme_sum_inequality_pos`): the concrete τ-theorem on `TensorObj`-style direct sums of matrix-multiplication tensors. Carved into platform-side first-class Theorem nodes via the τ-tree reductions.
-- source:
--   https://github.com/EntropyIncreaser/Prism

import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_mm_spectral
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_flattening
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_permutation
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_omega_pos
import Definitions.Def_mme_omega_normalize
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.PiTensorProduct

/-! # Bridge: concrete MME tensors ↔ the abstract asymptotic spectrum (MME)

Instantiates the abstract spectral theory of `Def_mme_mm_spectral` on the concrete tensor
quotient `TensorQ K 3`, with matrix-multiplication elements `MMq n m p = toQ (MMObj …)`,
and connects the abstract quantities to the concrete ones occurring in the goal:

* `mmTensorData K : MMData (TensorQ K 3) (tensorPreorder K)` — the bundle of MM structural
  facts (multiplicativity, monotonicity, bounds, cyclic spectrum symmetry);
* `bridge_asymptoticRank` — `asymptoticRank P (∑ MMq nᵢ mᵢ pᵢ) = tensorAsymptoticRank
  (bigAdd (MMObj …))`;
* `bridge_omega` — `(mmTensorData K).omegaAbs = matMulExp_strassen K`.

The structural facts and the two bridges are isolated as named `sorry` leaves with doc
comments; everything they feed into (`MMData.sum_inequality`) is sorry-free. -/

universe u

open MME BigOperators PiTensorProduct TensorProduct

namespace MME

variable {K : Type u} [Field K]

/-! ## A clean Strassen preorder on `TensorQ K 3` with reducible `le`

`TensorQ.tensorStrassen`'s structure projection to its `le` field does not reduce
definitionally when accessed from outside `Def_mme_tensor_quotient` (the auto-generated
equation lemma is broken: `(tensorStrassen …).le` cannot be rewritten to `TensorQ.le`).
Since downstream the `MMData` bundle needs `(tensorPreorder K).le (toQ X) (toQ Y)` to be
convertible to `TensorObj.Restrict X Y`, we rebuild the canonical preorder here directly
with the structure constructor (so `le := TensorQ.le` is reducible), re-deriving the six
restriction lemmas (`zeroObj`/`oneObj`/finite-decomposition + `⊕`/`⊗` functoriality).
`nat_order_embedding` reuses the public `diag_restrict_iff`. -/

namespace TensorQ

variable {d : ℕ}

/-- `f : X ← X'`, `g : Y ← Y'` induce `f ⊕ g : X⊕Y ← X'⊕Y'`. -/
private theorem add_restrict_aux' {X X' Y Y' : TensorObj K d}
    (hf : TensorObj.Restrict X X') (hg : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.add X Y) (TensorObj.add X' Y') := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨fun i => LinearMap.prodMap (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => LinearMap.prodMap (f i) (g i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X'.V i) (Y'.V i)) X'.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X'.V i) (Y'.V i)) Y'.t) =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t
  have h1 : (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ LinearMap.inl K (X'.V i) (Y'.V i)) =
            (fun i => LinearMap.inl K (X.V i) (Y.V i) ∘ₗ f i) := by
    funext i; ext x <;> simp [LinearMap.prodMap]
  have h2 : (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ LinearMap.inr K (X'.V i) (Y'.V i)) =
            (fun i => LinearMap.inr K (X.V i) (Y.V i) ∘ₗ g i) := by
    funext i; ext x <;> simp [LinearMap.prodMap]
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, h1, h2,
      PiTensorProduct.map_comp, PiTensorProduct.map_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, hf, hg]

private theorem interchange_tprod' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem map_interchange' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V₁ V₂ V₃ V₄ : ι → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i)) (interchange t₁ t₂) =
    interchange (PiTensorProduct.map f t₁) (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod', PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_tprod']
      simp only [TensorProduct.map_tmul]
    | add x y ih1 ih2 =>
      simp only [map_add, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

/-- `f : X ← X'`, `g : Y ← Y'` induce `f ⊗ g : X⊗Y ← X'⊗Y'`. -/
private theorem mul_restrict_aux' {X X' Y Y' : TensorObj K d}
    (hf : TensorObj.Restrict X X') (hg : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨fun i => TensorProduct.map (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
      (interchange X'.t Y'.t) = interchange X.t Y.t
  rw [map_interchange', hf, hg]

/-- `zeroObj` restricts to any `X` (zero maps; `d ≥ 1` kills every pure tensor). -/
private theorem restrict_zeroObj_le' (hd : 1 < d) (X : TensorObj K d) :
    TensorObj.Restrict TensorObj.zeroObj X := by
  have h0d : 0 < d := by omega
  refine ⟨fun _ => 0, ?_⟩
  show PiTensorProduct.map (fun i => (0 : X.V i →ₗ[K] PUnit)) X.t =
      (TensorObj.zeroObj : TensorObj K d).t
  show PiTensorProduct.map (fun i => (0 : X.V i →ₗ[K] PUnit)) X.t =
      (0 : PiTensorProduct K (fun _ : Fin d => PUnit))
  have hzero : (PiTensorProduct.map (fun i => (0 : X.V i →ₗ[K] PUnit)))
      = (0 : PiTensorProduct K X.V →ₗ[K] PiTensorProduct K (fun _ : Fin d => PUnit)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
    exact MultilinearMap.map_coord_zero (tprod K) ⟨0, h0d⟩ rfl
  rw [hzero, LinearMap.zero_apply]

/-- If `X.t = 0` then `toQ X = 0`. -/
private theorem toQ_eq_zero_of_t_eq_zero' (hd : 1 < d) {X : TensorObj K d} (hX : X.t = 0) :
    toQ X = (0 : TensorQ K d) := by
  apply Quotient.sound
  refine ⟨⟨fun _ => 0, ?_⟩, restrict_zeroObj_le' hd X⟩
  show PiTensorProduct.map (fun _ => (0 : (TensorObj.zeroObj : TensorObj K d).V _ →ₗ[K] X.V _))
      (TensorObj.zeroObj : TensorObj K d).t = X.t
  show PiTensorProduct.map _ (0 : PiTensorProduct K (fun _ : Fin d => PUnit)) = X.t
  rw [map_zero, hX]

private theorem cbre_map_coord' {X : TensorObj K d}
    {κ : Fin d → Type u} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) K (X.V i)) (p : ∀ i, κ i) :
    (constantBaseRingEquiv (Fin d) K)
        (PiTensorProduct.map (fun i => (b i).coord (p i)) X.t)
      = (Basis.piTensorProduct b).repr X.t p := by
  have key : ((constantBaseRingEquiv (Fin d) K).toLinearMap ∘ₗ
        PiTensorProduct.map (fun i => (b i).coord (p i)))
      = (Basis.piTensorProduct b).coord p := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, AlgEquiv.toLinearMap_apply, constantBaseRingEquiv_tprod,
      Module.Basis.coord_apply]
    exact (Basis.piTensorProduct_repr_tprod_apply b v p).symm
  have := LinearMap.congr_fun key X.t
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    Module.Basis.coord_apply] at this
  exact this

/-- If `X.t ≠ 0` then `oneObj` restricts to `X` (separating product functional). -/
private theorem restrict_oneObj_le_of_t_ne_zero' (hd : 1 < d) {X : TensorObj K d}
    (hX : X.t ≠ 0) : TensorObj.Restrict TensorObj.oneObj X := by
  have h0d : 0 < d := by omega
  let i₀ : Fin d := ⟨0, h0d⟩
  let κ : Fin d → Type u := fun i => Module.Free.ChooseBasisIndex K (X.V i)
  let b : ∀ i, Module.Basis (κ i) K (X.V i) := fun i => Module.Free.chooseBasis K (X.V i)
  let B := Basis.piTensorProduct b
  have hne : B.repr X.t ≠ 0 := fun h => hX (by
    have := B.sum_repr X.t; rw [h] at this; simpa using this.symm)
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hne
  rw [Finsupp.coe_zero, Pi.zero_apply] at hp
  set c := B.repr X.t p with hc
  let g₀ : ∀ i, X.V i →ₗ[K] K := fun i => (b i).coord (p i)
  let g : ∀ i, X.V i →ₗ[K] K := Function.update g₀ i₀ (c⁻¹ • g₀ i₀)
  refine ⟨g, ?_⟩
  show PiTensorProduct.map g X.t = (TensorObj.oneObj : TensorObj K d).t
  have hmap : PiTensorProduct.map g X.t = c⁻¹ • PiTensorProduct.map g₀ X.t := by
    have := PiTensorProduct.map_update_smul (f := g₀) i₀ c⁻¹ (g₀ i₀)
    rw [Function.update_eq_self] at this
    rw [show g = Function.update g₀ i₀ (c⁻¹ • g₀ i₀) from rfl, this, LinearMap.smul_apply]
  have hc0 : (constantBaseRingEquiv (Fin d) K) (PiTensorProduct.map g₀ X.t) = c :=
    cbre_map_coord' b p
  have hval : (constantBaseRingEquiv (Fin d) K) (PiTensorProduct.map g X.t) = 1 := by
    rw [hmap, map_smul, hc0, smul_eq_mul, inv_mul_cancel₀ hp]
  have hone : (constantBaseRingEquiv (Fin d) K) (TensorObj.oneObj : TensorObj K d).t = 1 := by
    show (constantBaseRingEquiv (Fin d) K) (tprod K (fun _ : Fin d => (1 : K))) = 1
    rw [constantBaseRingEquiv_tprod]; simp
  exact (constantBaseRingEquiv (Fin d) K).injective (hval.trans hone.symm)

/-- If `X.t = ∑ pure tensors` then `X` restricts to `diagObj N`. -/
private theorem restrict_diagObj_of_tprod_sum' {X : TensorObj K d} {N : ℕ}
    (w : Fin N → ∀ i, X.V i) (hX : X.t = ∑ n : Fin N, tprod K (w n)) :
    TensorObj.Restrict X (TensorObj.diagObj K d N) := by
  refine ⟨fun i => ∑ n : Fin N,
    LinearMap.smulRight (LinearMap.proj n : (Fin N → K) →ₗ[K] K) (w n i), ?_⟩
  have hf_eval : ∀ (i : Fin d) (k : Fin N),
      (∑ n : Fin N, LinearMap.smulRight (LinearMap.proj n : (Fin N → K) →ₗ[K] K) (w n i))
        (Pi.single k (1 : K)) = w k i := by
    intro i k
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun n _ hnk => by rw [Pi.single_eq_of_ne hnk, zero_smul])]
    simp
  show PiTensorProduct.map _ (TensorObj.diagObj K d N).t = X.t
  rw [hX]
  show PiTensorProduct.map _
      (∑ n : Fin N, PiTensorProduct.tprod K (fun _ => (Pi.single n 1 : Fin N → K))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  erw [PiTensorProduct.map_tprod]
  exact congrArg (PiTensorProduct.tprod K) (funext fun i => hf_eval i n)

/-- Every `X` restricts to some diagonal `diagObj N`. -/
private theorem exists_restrict_diagObj' (hd : 1 < d) (X : TensorObj K d) :
    ∃ N : ℕ, TensorObj.Restrict X (TensorObj.diagObj K d N) := by
  have h0d : 0 < d := by omega
  let i₀ : Fin d := ⟨0, h0d⟩
  let κ : Fin d → Type u := fun i => Module.Free.ChooseBasisIndex K (X.V i)
  let b : ∀ i, Module.Basis (κ i) K (X.V i) := fun i => Module.Free.chooseBasis K (X.V i)
  let B := Basis.piTensorProduct b
  haveI : Fintype (∀ i, κ i) := inferInstance
  let r := Fintype.card (∀ i, κ i)
  let e : (∀ i, κ i) ≃ Fin r := Fintype.equivFin _
  let w : (∀ i, κ i) → ∀ i, X.V i :=
    fun p i => if i = i₀ then (B.repr X.t p) • b i (p i) else b i (p i)
  have hw : ∀ p : ∀ i, κ i, (B.repr X.t p) • B p = tprod K (fun i => w p i) := by
    intro p
    rw [Basis.piTensorProduct_apply]
    set f := fun i : Fin d => b i (p i) with hf
    set cc := B.repr X.t p with hcc
    have hw_eq : (fun i => w p i) = Function.update f i₀ (cc • f i₀) := by
      funext i
      simp only [w, f]
      split_ifs with h
      · subst h; rw [Function.update_self]
      · exact (Function.update_of_ne h (cc • f i₀) f).symm
    rw [hw_eq, (tprod K (s := X.V)).map_update_smul f i₀ cc (f i₀), Function.update_eq_self]
  let v : Fin r → ∀ i, X.V i := fun j => w (e.symm j)
  have hsum : X.t = ∑ j : Fin r, tprod K (fun i => v j i) := by
    have hrepr : X.t = ∑ p : ∀ i, κ i, (B.repr X.t p) • B p := (B.sum_repr X.t).symm
    rw [hrepr]
    conv_lhs => arg 2; ext p; rw [hw p]
    exact (Fintype.sum_equiv e.symm _ _ (fun j => rfl)).symm
  exact ⟨r, restrict_diagObj_of_tprod_sum' v hsum⟩

end TensorQ

/-- The canonical Strassen preorder on order-3 tensors (`1 < 3`), built with reducible `le`
so that `(tensorPreorder K).le (toQ X) (toQ Y)` unfolds to `TensorObj.Restrict X Y`. -/
noncomputable def tensorPreorder (K : Type u) [Field K] : StrassenPreorder (TensorQ K 3) where
  toPreorder :=
    { le := TensorQ.le
      le_refl := TensorQ.le_refl
      le_trans := TensorQ.le_trans }
  add_right := by
    intro x y h z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact TensorQ.add_restrict_aux' h (TensorObj.Restrict.refl Z)
  mul_right := by
    intro x y h z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact TensorQ.mul_restrict_aux' h (TensorObj.Restrict.refl Z)
  zero_le := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact TensorQ.restrict_zeroObj_le' (by norm_num) X
  nat_order_embedding := by
    intro n m
    show TensorQ.le (TensorQ.toQ (TensorObj.diagObj K 3 n)) (TensorQ.toQ (TensorObj.diagObj K 3 m)) ↔ n ≤ m
    rw [TensorQ.le_toQ]
    exact diag_restrict_iff (by norm_num) n m
  lower_archimedean := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    by_cases hX : X.t = 0
    · left; exact TensorQ.toQ_eq_zero_of_t_eq_zero' (by norm_num) hX
    · right; exact TensorQ.restrict_oneObj_le_of_t_ne_zero' (by norm_num) hX
  upper_archimedean := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    obtain ⟨N, hN⟩ := TensorQ.exists_restrict_diagObj' (by norm_num) X
    exact ⟨N, hN⟩

/-- The matrix-multiplication element `⟨n,m,p⟩` in the tensor quotient. -/
noncomputable def MMq (K : Type u) [Field K] (n m p : ℕ) : TensorQ K 3 :=
  TensorQ.toQ (MMObj K n m p)

/-! ### Helpers: the MM pure tensor and the unfolded `MMObj.t` -/

/-- The pure tensor `e_{ij} ⊗ e_{jk} ⊗ e_{ki}` for indices `(i,j,k)`. -/
noncomputable def MMPure (K : Type u) [Field K] (n m p : ℕ) (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  PiTensorProduct.tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

theorem MMObj_t (n m p : ℕ) :
    (MMObj K n m p).t = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k := rfl

/-- The canonical Strassen preorder's `le` on quotient classes is `TensorObj.Restrict`. -/
theorem tensorPreorder_le_toQ (X Y : TensorObj K 3) :
    (tensorPreorder K).le (TensorQ.toQ X) (TensorQ.toQ Y) ↔ TensorObj.Restrict X Y :=
  TensorQ.le_toQ X Y

/-! ## Structural MM facts on the quotient (deep leaves)

Each is the quotient-level shadow of a concrete `MMObj` isomorphism/restriction. They
mirror the Prism `MatrixMult.lean` lemmas (`MM_one`, `MM_mul`, `MM_le_of_le`, `MM_le_mul`,
`MM_ne_zero`) and the cyclic permutation symmetry. -/

/-- `⟨1,1,1⟩ = 1`: `MMObj 1 1 1 ≅ oneObj` (port of Prism `MM_one`; each mode
`Fin 1 × Fin 1 → K ≅ K`). -/
theorem MMq_one : MMq K 1 1 1 = 1 := by
  show TensorQ.toQ (MMObj K 1 1 1) = (1 : TensorQ K 3)
  rw [TensorQ.toQ_one]
  apply Quotient.sound
  -- mode-wise: `oneObj.V i = K`, `(MMObj 1 1 1).V i = Fin 1 × Fin 1 → K` (constant functions)
  let toMM : ∀ i : Fin 3, (TensorObj.oneObj : TensorObj K 3).V i →ₗ[K] (MMObj K 1 1 1).V i
    | ⟨0, _⟩ => { toFun := fun c _ => c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨1, _⟩ => { toFun := fun c _ => c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨2, _⟩ => { toFun := fun c _ => c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨_ + 3, h⟩ => absurd h (by omega)
  let toOne : ∀ i : Fin 3, (MMObj K 1 1 1).V i →ₗ[K] (TensorObj.oneObj : TensorObj K 3).V i
    | ⟨0, _⟩ => { toFun := fun f => f (0, 0), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨1, _⟩ => { toFun := fun f => f (0, 0), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨2, _⟩ => { toFun := fun f => f (0, 0), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨_ + 3, h⟩ => absurd h (by omega)
  constructor
  · -- Restrict (MMObj 1 1 1) oneObj: map toMM oneObj.t = (MMObj 1 1 1).t
    refine ⟨toMM, ?_⟩
    show PiTensorProduct.map toMM (TensorObj.oneObj : TensorObj K 3).t = (MMObj K 1 1 1).t
    show PiTensorProduct.map toMM (tprod K (fun _ : Fin 3 => (1 : K))) = (MMObj K 1 1 1).t
    erw [PiTensorProduct.map_tprod]; rw [MMObj_t]
    rw [Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    show _ = MMPure K 1 1 1 0 0 0
    simp only [MMPure]
    congr 1; funext s; fin_cases s <;>
      (funext ab; obtain ⟨a, b⟩ := ab;
       rw [Subsingleton.elim a 0, Subsingleton.elim b 0];
       simp only [toMM, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same];
       try (first | rfl | (erw [LinearMap.coe_mk, AddHom.coe_mk]; simp)))
  · -- Restrict oneObj (MMObj 1 1 1): map toOne (MMObj 1 1 1).t = oneObj.t
    refine ⟨toOne, ?_⟩
    show PiTensorProduct.map toOne (MMObj K 1 1 1).t = (TensorObj.oneObj : TensorObj K 3).t
    rw [MMObj_t, Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    show PiTensorProduct.map toOne (MMPure K 1 1 1 0 0 0) = tprod K (fun _ : Fin 3 => (1 : K))
    simp only [MMPure]
    erw [PiTensorProduct.map_tprod]
    congr 1; funext s; fin_cases s <;>
      (simp only [toOne, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same];
       try (first | rfl | (erw [LinearMap.coe_mk, AddHom.coe_mk]; simp)))

/-- Curry/uncurry for function types on product domains. -/
private def uncurryEquiv (α β γ : Type*) [AddCommGroup γ] [Module K γ] :
    (α → β → γ) ≃ₗ[K] (α × β → γ) where
  toFun f p := f p.1 p.2
  map_add' _ _ := by funext ⟨_, _⟩; rfl
  map_smul' _ _ := by funext ⟨_, _⟩; rfl
  invFun f a b := f (a, b)
  left_inv _ := by funext _ _; rfl
  right_inv _ := by funext ⟨_, _⟩; rfl

/-- Kronecker mode equiv `(Fin a × Fin b → K) ⊗ (Fin c × Fin d → K) ≃ (Fin (a*c) × Fin (b*d) → K)`
(port of Prism `kronEquiv`). -/
private noncomputable def kronEquiv (a b c d : ℕ) :
    ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
  let e2 : ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin c × Fin d → (Fin a × Fin b → K)) :=
    TensorProduct.piScalarRight K K (Fin a × Fin b → K) (Fin c × Fin d)
  let e3 : (Fin c × Fin d → (Fin a × Fin b → K)) ≃ₗ[K]
      ((Fin c × Fin d) × (Fin a × Fin b) → K) :=
    uncurryEquiv (K := K) (Fin c × Fin d) (Fin a × Fin b) K
  let reindex : (Fin a × Fin c) × (Fin b × Fin d) ≃ (Fin c × Fin d) × (Fin a × Fin b) :=
    (Equiv.prodProdProdComm (Fin a) (Fin c) (Fin b) (Fin d)).trans (Equiv.prodComm _ _)
  let e4 : ((Fin c × Fin d) × (Fin a × Fin b) → K) ≃ₗ[K]
      ((Fin a × Fin c) × (Fin b × Fin d) → K) :=
    LinearEquiv.funCongrLeft K K reindex
  let e5 : ((Fin a × Fin c) × (Fin b × Fin d) → K) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
    LinearEquiv.funCongrLeft K K
      (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  e2.trans (e3.trans (e4.trans e5))

/-- Action of `kronEquiv` on a pure tensor of basis elements (port of Prism `kronEquiv_single`). -/
private theorem kronEquiv_single {a b c d : ℕ}
    (i : Fin a) (j : Fin b) (i' : Fin c) (j' : Fin d) :
    kronEquiv (K := K) a b c d ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1)) =
      Pi.single (finProdFinEquiv (i, i'), finProdFinEquiv (j, j')) 1 := by
  funext IJ; obtain ⟨I, J⟩ := IJ
  have lhs_val :
      ((kronEquiv (K := K) a b c d)
          ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1))) (I, J) =
        ((Pi.single (i', j') 1 : Fin c × Fin d → K)
            ((finProdFinEquiv.symm I).2, (finProdFinEquiv.symm J).2)) *
          ((Pi.single (i, j) 1 : Fin a × Fin b → K)
            ((finProdFinEquiv.symm I).1, (finProdFinEquiv.symm J).1)) := by
    simp only [kronEquiv, uncurryEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_mk,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.trans_apply,
      Equiv.prodProdProdComm_apply, Equiv.prodComm_apply, Prod.swap]
    rfl
  rw [lhs_val]
  simp only [Pi.single_apply, Prod.mk.injEq]
  set I' : Fin a × Fin c := finProdFinEquiv.symm I with hIdef
  set J' : Fin b × Fin d := finProdFinEquiv.symm J with hJdef
  have hIeq : I = finProdFinEquiv I' := by rw [hIdef]; exact (finProdFinEquiv.apply_symm_apply I).symm
  have hJeq : J = finProdFinEquiv J' := by rw [hJdef]; exact (finProdFinEquiv.apply_symm_apply J).symm
  rw [hIeq, hJeq]
  simp only [finProdFinEquiv.injective.eq_iff]
  obtain ⟨I'1, I'2⟩ := I'
  obtain ⟨J'1, J'2⟩ := J'
  by_cases hI2 : I'2 = i'
  · by_cases hJ2 : J'2 = j'
    · by_cases hI1 : I'1 = i
      · by_cases hJ1 : J'1 = j
        · simp [hI1, hI2, hJ1, hJ2]
        · simp [hI1, hI2, hJ1, hJ2]
      · simp [hI1, hI2, hJ2]
    · simp [hJ2, hI2]
  · simp [hI2]

/-- Multiplicativity. DEEP LEAF: `MMObj n m p ⊗ MMObj n' m' p' ≅ MMObj (nn') (mm') (pp')`
via the Kronecker mode equivalences (Prism `MM_mul`, `kronEquiv`).  The per-mode equivalence
`kronEquiv`/`kronEquiv_single` and the per-term image `map equiv (interchange e e') = MMPure …`
are established (see the helpers above); the remaining step is the bilinear distribution of
`map ∘ interchange` over the two triple sums plus the index reindexing. -/
theorem MMq_mul (n m p n' m' p' : ℕ) :
    MMq K n m p * MMq K n' m' p' = MMq K (n * n') (m * m') (p * p') := by
  show TensorQ.toQ (MMObj K n m p) * TensorQ.toQ (MMObj K n' m' p') =
      TensorQ.toQ (MMObj K (n * n') (m * m') (p * p'))
  rw [← TensorQ.toQ_kron]
  exact Quotient.sound (MMObj_kron_iso n m p n' m' p')

/-- `MMObj n m p` restricts to `MMObj n' m' p'` when `n ≤ n'`, `m ≤ m'`, `p ≤ p'`.
Port of Prism `MM_le_of_le`: the mode-wise restriction maps precompose with the index
inclusions `Fin n × Fin m ↪ Fin n' × Fin m'`, etc. -/
theorem MMObj_restrict_of_le {n n' m m' p p' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (hp : p ≤ p') :
    TensorObj.Restrict (MMObj K n m p) (MMObj K n' m' p') := by
  let f₀ : (MMObj K n' m' p').V 0 →ₗ[K] (MMObj K n m p).V 0 :=
    LinearMap.funLeft K K (fun ab : Fin n × Fin m => (Fin.castLE hn ab.1, Fin.castLE hm ab.2))
  let f₁ : (MMObj K n' m' p').V 1 →ₗ[K] (MMObj K n m p).V 1 :=
    LinearMap.funLeft K K (fun ab : Fin m × Fin p => (Fin.castLE hm ab.1, Fin.castLE hp ab.2))
  let f₂ : (MMObj K n' m' p').V 2 →ₗ[K] (MMObj K n m p).V 2 :=
    LinearMap.funLeft K K (fun ab : Fin p × Fin n => (Fin.castLE hp ab.1, Fin.castLE hn ab.2))
  let hf : ∀ s : Fin 3, (MMObj K n' m' p').V s →ₗ[K] (MMObj K n m p).V s :=
    fun s => Fin.cases f₀ (fun s => Fin.cases f₁ (fun s => Fin.cases f₂
      (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨hf, ?_⟩
  have key : ∀ (i : Fin n) (j : Fin m) (k : Fin p),
      PiTensorProduct.map hf (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) (Fin.castLE hp k)) =
      MMPure K n m p i j k := by
    intro i j k
    simp only [MMPure, hf, f₀, f₁, f₂]
    erw [PiTensorProduct.map_tprod]
    congr 1; funext s; fin_cases s
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hn i, Fin.castLE hm j) 1) = Pi.single (i, j) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hm j, Fin.castLE hp k) 1) = Pi.single (j, k) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change (LinearMap.funLeft K K _) (Pi.single (Fin.castLE hp k, Fin.castLE hn i) 1) = Pi.single (k, i) 1
      funext ⟨a, b⟩; rw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
  have h_out : ∀ (i' : Fin n') (j' : Fin m') (k' : Fin p'),
      (¬ i'.val < n ∨ ¬ j'.val < m ∨ ¬ k'.val < p) →
      PiTensorProduct.map hf (MMPure K n' m' p' i' j' k') = 0 := by
    intro i' j' k' h
    dsimp only [f₀, f₁, f₂, hf, MMPure]
    erw [PiTensorProduct.map_tprod]
    rcases h with h | h | h
    · apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin n × Fin m => (Fin.castLE hn ab.1, Fin.castLE hm ab.2))
        (Pi.single (i', j') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin m × Fin p => (Fin.castLE hm ab.1, Fin.castLE hp ab.2))
        (Pi.single (j', k') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin p × Fin n => (Fin.castLE hp ab.1, Fin.castLE hn ab.2))
        (Pi.single (k', i') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
  show PiTensorProduct.map hf (MMObj K n' m' p').t = (MMObj K n m p).t
  rw [MMObj_t, MMObj_t]
  have sum_le : ∀ {M : Type u} [AddCommMonoid M] (n1 n2 : ℕ) (h12 : n1 ≤ n2) (f : Fin n2 → M)
      (hf0 : ∀ i : Fin n2, ¬ i.val < n1 → f i = 0),
      ∑ i : Fin n2, f i = ∑ i : Fin n1, f (Fin.castLE h12 i) := by
    intro M _ n1 n2 h12 f hf0
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
    rw [Fin.sum_univ_add]
    have tail_zero : ∑ i : Fin d, f (Fin.natAdd n1 i) = 0 :=
      Finset.sum_eq_zero (fun i _ => hf0 _ (by simp [Fin.natAdd]))
    have step : ∑ i : Fin n1, f (Fin.castAdd d i) = ∑ i : Fin n1, f (Fin.castLE h12 i) :=
      Finset.sum_congr rfl fun i _ => by congr 1
    simp [tail_zero, step]
  have step1 : ∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' i j k) =
      ∑ i : Fin n, ∑ j : Fin m', ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k) :=
    sum_le n n' hn _ (fun i' hi' =>
      Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun k' _ => h_out i' j' k' (Or.inl hi'))))
  have step2 : ∀ i : Fin n,
      ∑ j : Fin m', ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k) =
      ∑ j : Fin m, ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) :=
    fun i => sum_le m m' hm _ (fun j' hj' =>
      Finset.sum_eq_zero (fun k' _ => h_out (Fin.castLE hn i) j' k' (Or.inr (Or.inl hj'))))
  have step3 : ∀ (i : Fin n) (j : Fin m),
      ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) =
      ∑ k : Fin p, MMPure K n m p i j k :=
    fun i j => by
      rw [sum_le p p' hp _ (fun k' hk' => h_out (Fin.castLE hn i) (Fin.castLE hm j) k' (Or.inr (Or.inr hk')))]
      apply Finset.sum_congr rfl; intro k _; exact key i j k
  have step0 : PiTensorProduct.map hf (∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', MMPure K n' m' p' i j k)
      = ∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', (PiTensorProduct.map hf) (MMPure K n' m' p' i j k) := by
    simp only [map_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => map_sum _ _ _
  have step4 : ∑ i : Fin n, ∑ j : Fin m', ∑ k : Fin p',
        (PiTensorProduct.map hf) (MMPure K n' m' p' (Fin.castLE hn i) j k)
      = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k := by
    apply Finset.sum_congr rfl; intro i _
    rw [step2]; apply Finset.sum_congr rfl; intro j _
    exact step3 i j
  exact step0.trans (step1.trans step4)

/-- Monotonicity. Restriction maps from index inclusions (Prism `MM_le_of_le`). -/
theorem MMq_le_of_le {n n' m m' p p' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (hp : p ≤ p') :
    (tensorPreorder K).le (MMq K n m p) (MMq K n' m' p') :=
  (tensorPreorder_le_toQ (MMObj K n m p) (MMObj K n' m' p')).mpr (MMObj_restrict_of_le hn hm hp)

/-- `MMObj n m p` restricts to the diagonal `diagObj K 3 (n*m*p)`: its tensor element is a
sum of exactly `n*m*p` pure tensors (port of Prism `MM_le_mul`). -/
theorem MMObj_restrict_diag (n m p : ℕ) :
    TensorObj.Restrict (MMObj K n m p) (TensorObj.diagObj K 3 (n * m * p)) := by
  let e : Fin (n * m * p) ≃ Fin n × Fin m × Fin p :=
    finProdFinEquiv.symm.trans
      (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _) |>.trans (Equiv.prodAssoc _ _ _))
  refine TensorQ.restrict_diagObj_of_tprod_sum' (fun idx (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single ((e idx).1, (e idx).2.1) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single ((e idx).2.1, (e idx).2.2) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single ((e idx).2.2, (e idx).1) 1 : Fin p × Fin n → K)) ?_
  rw [MMObj_t]
  rw [show (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPure K n m p i j k) =
      ∑ ijk : Fin n × Fin m × Fin p, MMPure K n m p ijk.1 ijk.2.1 ijk.2.2 from by
    simp_rw [← Finset.sum_product']; rfl]
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Trivial bound. `MMObj n m p ≤ I_{nmp}` (Prism `MM_le_mul`). -/
theorem MMq_le_mul (n m p : ℕ) :
    (tensorPreorder K).le (MMq K n m p) ((n * m * p : ℕ) : TensorQ K 3) :=
  (tensorPreorder_le_toQ (MMObj K n m p) (TensorObj.diagObj K 3 (n * m * p))).mpr
    (MMObj_restrict_diag n m p)

/-- Nonvanishing for positive dimensions. `1 ≤ MMObj n m p` and `nat_order_embedding`
(Prism `MM_ne_zero`). -/
theorem MMq_ne_zero {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    MMq K n m p ≠ 0 := by
  intro h
  -- `1 = MMq 1 1 1 ≤ MMq n m p = 0`, contradicting `nat_order_embedding`.
  have h1 : (tensorPreorder K).le (MMq K 1 1 1) (MMq K n m p) := MMq_le_of_le hn hm hp
  rw [MMq_one, h] at h1
  have h1' : (tensorPreorder K).le ((1 : ℕ) : TensorQ K 3) ((0 : ℕ) : TensorQ K 3) := by
    have e1 : ((1 : ℕ) : TensorQ K 3) = (1 : TensorQ K 3) := Nat.cast_one
    have e0 : ((0 : ℕ) : TensorQ K 3) = (0 : TensorQ K 3) := Nat.cast_zero
    rw [e1, e0]; exact h1
  have : (1 : ℕ) ≤ 0 := ((tensorPreorder K).nat_order_embedding 1 0).mp h1'
  exact Nat.not_succ_le_zero 0 this

/-- Cyclic spectrum symmetry. DEEP LEAF: cyclic mode permutation
`permuteSpaces` sends `MMObj n m p` to `MMObj p n m` and induces a spectrum-point map
`φ ↦ φ^c` with `φ^c(⟨n,m,p⟩) = φ(⟨p,n,m⟩)` (Prism `MM_permuteSpaces_cyclic`,
`AsymptoticSpectrumPoint.perm`, `θ_perm_cyclic`). -/
theorem MMq_cyclic (φ : AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K)) :
    ∃ φ' : AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K),
      ∀ n m p : ℕ, φ' (MMq K n m p) = φ (MMq K p n m) := by
  -- The permuted spectrum point `φ' := φ ∘ permAut cyclicPerm`.
  refine ⟨{ toRingHom := φ.toRingHom.comp (TensorQ.permAut cyclicPerm)
            monotone' := fun {a b} hab => φ.monotone' (TensorQ.permAut_le cyclicPerm hab) }, ?_⟩
  intro n m p
  show φ.toRingHom (TensorQ.permAut cyclicPerm (TensorQ.toQ (MMObj K n m p))) = φ (MMq K p n m)
  rw [permAut_MMq]
  rfl

/-- The bundle of MM facts, instantiating the abstract spectral framework. -/
noncomputable def mmTensorData (K : Type u) [Field K] :
    MMData (TensorQ K 3) (tensorPreorder K) where
  MMel := MMq K
  one := MMq_one
  mul := MMq_mul
  le_of_le := fun hn hm hp => MMq_le_of_le hn hm hp
  le_mul := MMq_le_mul
  ne_zero := fun hn hm hp => MMq_ne_zero hn hm hp
  cyclic := MMq_cyclic

/-! ## The two analytic bridges (deep leaves) -/

/-- **Bridge A** (deep leaf): the abstract asymptotic rank of the sum of MM quotient
elements equals the concrete asymptotic rank of the direct sum of `MMObj`s.

This packages two facts: (i) `bigAdd (MMObj …)` maps under `toQ` to `∑ MMq …` (direct
sum descends to `+`); (ii) `tensorRankObj` of a `TensorObj` equals `rank` of its class
(both = least `r` with a restriction to `I_r`), hence `tensorAsymptoticRank` equals the
abstract `asymptoticRank`. NEEDS: `bigAdd`/`kronPow` ↔ `∑`/`^` descent plus the
`rank = tensorRankObj` characterization (Prism `tensor_le_natCast_iff`). -/
theorem bridge_asymptoticRank {k : ℕ} (n m p : Fin k → ℕ) :
    StrassenPreorder.asymptoticRank (tensorPreorder K)
        (∑ i, MMq K (n i) (m i) (p i)) =
      tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by
  have hd : (1 : ℕ) < 3 := by norm_num
  -- `tensorPreorder` and the quotient's canonical `tensorStrassen` have the same `le`.
  have heq : tensorPreorder K = TensorQ.tensorStrassen K 3 hd :=
    StrassenPreorder.ext (fun _ _ => Iff.rfl)
  rw [heq, TensorQ.tensorAsymptoticRank_eq hd, TensorQ.toQ_bigAdd]
  rfl

/-- **Bridge B** (deep leaf): the abstract MM exponent equals the Strassen-form `ω`.

`(mmTensorData K).omegaAbs = ⨆_φ (θ₁+θ₂+θ₃)(φ)`, which by duality equals
`log₂ AR(MM 2 2 2)`, which equals `matMulExp_strassen K = ⨅ₙ log(strassenRank
(MMTensor n n n))/log n`. NEEDS: the canonical normalization `ω = log₂ AR(MM 2 2 2)`
(Prism `matMulExp_eq_log_AR_222`) and the `strassenRank ↔ rank` identification. -/
theorem bridge_omega : (mmTensorData K).omegaAbs = matMulExp_strassen K := by
  -- `θsum φ := θ₁ + θ₂ + θ₃`, and `omegaAbs = ⨆ φ, θsum φ` by definition.
  set θsum : AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K) → ℝ :=
    fun φ => (mmTensorData K).θ₁ φ + (mmTensorData K).θ₂ φ + (mmTensorData K).θ₃ φ with hθsum
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The spectrum is compact and `θsum` is continuous, so it attains a maximum.
  have : Nonempty (AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K)) :=
    mme_spectrum_nonempty (tensorPreorder K)
  have h_compact :
      IsCompact (Set.univ : Set (AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K))) :=
    isCompact_univ
  obtain ⟨φ_max, -, hmax⟩ :=
    h_compact.exists_isMaxOn Set.univ_nonempty (mmTensorData K).continuous_θsum.continuousOn
  -- `omegaAbs = θsum φ_max`.
  have h_omega_max : (mmTensorData K).omegaAbs = θsum φ_max := by
    apply le_antisymm
    · refine ciSup_le ?_; intro φ; exact hmax (Set.mem_univ φ)
    · exact le_ciSup (f := θsum)
        ⟨θsum φ_max, fun y ⟨φ, hφ⟩ => hφ ▸ hmax (Set.mem_univ φ)⟩ φ_max
  -- Each spectrum point evaluates `MMq 2 2 2` to `2 ^ (θsum φ)`.
  have h_eval : ∀ φ : AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K),
      φ (MMq K 2 2 2) = (2 : ℝ) ^ (θsum φ) := by
    intro φ
    -- `(mmTensorData K).MMel 2 2 2 = MMq K 2 2 2` definitionally.
    have h := (mmTensorData K).MM_eval φ (n := 2) (m := 2) (p := 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [show (mmTensorData K).MMel 2 2 2 = MMq K 2 2 2 from rfl] at h
    rw [h, hθsum]
    -- `2^θ₁ * 2^θ₂ * 2^θ₃ = 2^(θ₁+θ₂+θ₃)`.
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  -- Spectrum-point evaluations of `MMq 2 2 2` are bounded above (by `2 ^ θsum φ_max`).
  have h_bddAbove : BddAbove (Set.range
      (fun φ : AsymptoticSpectrumPoint (TensorQ K 3) (tensorPreorder K) => φ (MMq K 2 2 2))) := by
    refine ⟨(2 : ℝ) ^ (θsum φ_max), ?_⟩
    rintro _ ⟨φ, rfl⟩
    show φ (MMq K 2 2 2) ≤ (2 : ℝ) ^ (θsum φ_max)
    rw [h_eval φ]
    exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr (hmax (Set.mem_univ φ))
  -- Piece (1): the spectral identity, via duality + the maximizing point.
  have hpiece1 : StrassenPreorder.asymptoticRank (tensorPreorder K) (MMq K 2 2 2) =
      (2 : ℝ) ^ (mmTensorData K).omegaAbs := by
    rw [mme_strassen_duality (tensorPreorder K) (MMq K 2 2 2)]
    -- `⨆ φ, φ(MMq) = ⨆ φ, 2^(θsum φ) = 2^(θsum φ_max) = 2^omegaAbs`.
    rw [h_omega_max]
    apply le_antisymm
    · -- `⨆ φ, φ(MMq) ≤ 2^(θsum φ_max)`.
      refine ciSup_le (fun φ => ?_)
      rw [h_eval φ]
      exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr (hmax (Set.mem_univ φ))
    · -- `2^(θsum φ_max) = φ_max(MMq) ≤ ⨆ φ, φ(MMq)`.
      rw [← h_eval φ_max]
      exact le_ciSup h_bddAbove φ_max
  -- Piece (2): AR identification (mirror `bridge_asymptoticRank`'s `heq` reconciliation).
  have hd : (1 : ℕ) < 3 := by norm_num
  have heq : tensorPreorder K = TensorQ.tensorStrassen K 3 hd :=
    StrassenPreorder.ext (fun _ _ => Iff.rfl)
  have hpiece2 : tensorAsymptoticRank (MMObj K 2 2 2) =
      StrassenPreorder.asymptoticRank (tensorPreorder K) (MMq K 2 2 2) := by
    rw [heq, TensorQ.tensorAsymptoticRank_eq hd (MMObj K 2 2 2)]
    rfl
  -- Piece (3): concrete normalization.
  have hpiece3 : matMulExp_strassen K =
      Real.log (tensorAsymptoticRank (MMObj K 2 2 2)) / Real.log 2 :=
    matMulExp_strassen_eq_log_AR
  -- Chain: ω = log(AR(MMObj))/log 2 = log(AR(MMq))/log 2 = log(2^omegaAbs)/log 2 = omegaAbs.
  rw [hpiece3, hpiece2, hpiece1, Real.log_rpow (by norm_num : (0:ℝ) < 2),
      mul_div_assoc, div_self (ne_of_gt hlog2_pos), mul_one]

/-! ## The concrete sum inequality (the goal shape) -/

/-- **The all-positive concrete sum inequality**, assembled sorry-free from the abstract
`MMData.sum_inequality` and the two bridges. -/
theorem mme_sum_inequality_pos {k : ℕ} (n m p : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by
  -- Translate the hypothesis to the abstract asymptotic rank via bridge A.
  have h' : StrassenPreorder.asymptoticRank (tensorPreorder K)
      (∑ i, MMq K (n i) (m i) (p i)) ≤ r := by
    rw [bridge_asymptoticRank n m p]; exact h
  -- Run the abstract sum inequality.
  have hsum := (mmTensorData K).sum_inequality n m p hn hm hp r ?_
  · -- Replace `omegaAbs` by `matMulExp_strassen K`.
    rwa [bridge_omega] at hsum
  · -- `MMData.MMel = MMq K`, so the abstract sum is exactly `∑ MMq`.
    show StrassenPreorder.asymptoticRank (tensorPreorder K)
      (∑ i, (mmTensorData K).MMel (n i) (m i) (p i)) ≤ r
    exact h'

/-- `MMTensor K n m p = 0` whenever one of the dimensions is `0` (the defining triple sum
runs over an empty `Fin 0` index). -/
theorem MMTensor_eq_zero_of_zero_dim {n m p : ℕ} (h : n = 0 ∨ m = 0 ∨ p = 0) :
    MMTensor K n m p = 0 := by
  rw [MMTensor]
  rcases h with hn | hm | hp
  · subst hn; exact Fin.sum_univ_zero _
  · subst hm
    exact Finset.sum_eq_zero (fun i _ => Fin.sum_univ_zero _)
  · subst hp
    exact Finset.sum_eq_zero (fun i _ =>
      Finset.sum_eq_zero (fun j _ => Fin.sum_univ_zero _))

/-- `MMq K n m p = 0` whenever one of the dimensions is `0`: the corresponding `MMObj`
is the zero tensor, so its class in `TensorQ K 3` is `0`. -/
theorem MMq_eq_zero_of_not_pos {n m p : ℕ} (h : ¬ (1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ p)) :
    MMq K n m p = 0 := by
  have hzero : n = 0 ∨ m = 0 ∨ p = 0 := by omega
  show TensorQ.toQ (MMObj K n m p) = 0
  exact TensorQ.toQ_eq_zero_of_t_eq_zero' (by norm_num)
    (show (MMObj K n m p).t = 0 from MMTensor_eq_zero_of_zero_dim hzero)

/-- **Reduction to positive dimensions**. The goal allows zero dimensions, but the
asymptotic-spectrum argument needs `1 ≤ nᵢ, mᵢ, pᵢ`. When some dimension is `0` the
corresponding `MMObj` is the zero tensor, so its quotient class `MMq` is `0` and it drops
out of the abstract sum without changing the asymptotic rank; correspondingly
`(nᵢmᵢpᵢ)^(ω/3) = 0^(ω/3) = 0` (using `ω/3 > 0`) so the real summand vanishes too. Hence
the general case reduces to the all-positive case `mme_sum_inequality_pos` applied to the
positive subfamily reindexed onto `Fin S.card`. -/
theorem mme_sum_inequality {k : ℕ} (n m p : Fin k → ℕ) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by
  classical
  -- The positive subfamily `S` and its reindexing `e : Fin S.card ≃ {x // x ∈ S}`.
  set S : Finset (Fin k) := Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) with hS
  set e : Fin S.card ≃ {x // x ∈ S} := (S.equivFin).symm with he
  -- Positivity holds on the reindexed family.
  have hmemS : ∀ x : {x // x ∈ S}, 1 ≤ n x.1 ∧ 1 ≤ m x.1 ∧ 1 ≤ p x.1 := by
    intro x
    have hx : x.1 ∈ Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := hS ▸ x.2
    exact (Finset.mem_filter.mp hx).2
  have hn' : ∀ j : Fin S.card, 1 ≤ n (e j).1 := fun j => (hmemS (e j)).1
  have hm' : ∀ j : Fin S.card, 1 ≤ m (e j).1 := fun j => (hmemS (e j)).2.1
  have hp' : ∀ j : Fin S.card, 1 ≤ p (e j).1 := fun j => (hmemS (e j)).2.2
  -- KEY (tensor side): the abstract sum over the positive subfamily equals the abstract
  -- sum over the full family, because the off-`S` `MMq` terms are `0`.
  have hsum_eq :
      (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1))
        = ∑ i, MMq K (n i) (m i) (p i) := by
    rw [show (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1))
          = ∑ x : {x // x ∈ S}, MMq K (n x.1) (m x.1) (p x.1) from
        Equiv.sum_comp e (fun x => MMq K (n x.1) (m x.1) (p x.1))]
    rw [Finset.sum_coe_sort S (fun i => MMq K (n i) (m i) (p i))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    exact MMq_eq_zero_of_not_pos (fun hpos => hi ⟨Finset.mem_univ i, hpos⟩)
  -- Transport `h` to the positive subfamily via `bridge_asymptoticRank` (both directions).
  have h' : tensorAsymptoticRank
      (TensorObj.bigAdd (fun j => MMObj K (n (e j).1) (m (e j).1) (p (e j).1))) ≤ r := by
    rw [← bridge_asymptoticRank (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1),
        hsum_eq, bridge_asymptoticRank n m p]
    exact h
  -- Run the all-positive case on the reindexed subfamily.
  have hpos := mme_sum_inequality_pos
    (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1) hn' hm' hp' r h'
  -- KEY (real side): the subfamily sum equals the full sum (off-`S` summands are `0^(ω/3)`).
  have hexp_ne : matMulExp_strassen K / 3 ≠ 0 := by
    have := matMulExp_strassen_pos (K := K); positivity
  have hreal_eq :
      (∑ j : Fin S.card, ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))
        = ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) := by
    rw [show (∑ j : Fin S.card,
            ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))
          = ∑ x : {x // x ∈ S},
            ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) from
        Equiv.sum_comp e
          (fun x => ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    rw [Finset.sum_coe_sort S
      (fun i => ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    have hnp : ¬ (1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := fun hpos => hi ⟨Finset.mem_univ i, hpos⟩
    have hzero : n i * m i * p i = 0 := by
      rcases (by omega : n i = 0 ∨ m i = 0 ∨ p i = 0) with h0 | h0 | h0 <;>
        simp [h0]
    rw [hzero, Nat.cast_zero, Real.zero_rpow hexp_ne]
  rwa [hreal_eq] at hpos

end MME


