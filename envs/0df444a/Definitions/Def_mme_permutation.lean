-- Prove2me | Definitions.Def_mme_permutation
-- name    : mme_permutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:38:15.36107+00:00
-- url     : https://prove2.me/theorems/255ab518-11a7-4c43-9747-18f3c442b466
-- statement:
--   **Cyclic mode-permutation machinery on `TensorObj` and `TensorQ`.**
--
--   Reusable infrastructure for the cyclic spectrum symmetry of matrix-multiplication tensors, used by `Def_mme_tensor_bridge`'s `MMq_cyclic` (`MMq\,n\,m\,p \sim MMq\,p\,n\,m` in the quotient).
--
--   **Permutation of modes.** For $\sigma : \mathrm{Sym}(\mathrm{Fin}\,d)$ and $X : \mathrm{TensorObj}\,K\,d$:
--   - `TensorObj.permObj σ X` reindexes $X$'s mode spaces: $(\mathrm{permObj}\,\sigma\,X).V\,i = X.V(\sigma^{-1}\,i)$ and the element is transported via `PiTensorProduct.reindex`.
--   - `permObj_restrict` / `permObj_isomorphic` — `permObj σ` preserves restriction (hence isomorphism), so it descends to `TensorQ`.
--
--   **Cyclic shift of matrix-multiplication tensors.** `MMObj_permObj_cyclic`: for the 3-cycle $\sigma = (1\;2\;3)$ on $\mathrm{Fin}\,3$,
--   $$\mathrm{permObj}\,\sigma\,(\mathrm{MMObj}\,n\,m\,p) \;\cong\; \mathrm{MMObj}\,p\,n\,m.$$
--   Geometrically, cyclically shifting the three modes of the matrix-multiplication tensor cyclically shifts the three dimension parameters.
--
--   **Quotient ring homomorphism.** `TensorQ.permAut σ` is the descent of `permObj σ` to `TensorQ K 3`, bundled as a **ring homomorphism** $\mathrm{TensorQ}\,K\,3 \to_{+\,\cdot} \mathrm{TensorQ}\,K\,3$ (it respects `+`, `*`, `0`, `1`). Comes with:
--   - `permAut_le` — monotone for the restriction order;
--   - `permAut_MMq` — explicit formula $\mathrm{permAut}\,\mathrm{cyclicPerm}\,(\mathrm{toQ}\,(\mathrm{MMObj}\,n\,m\,p)) = \mathrm{toQ}\,(\mathrm{MMObj}\,p\,n\,m)$.

import Mathlib.GroupTheory.Perm.Basic
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_quotient

/-! # Cyclic mode-permutation machinery on `TensorObj`/`TensorQ` (MME)

This file provides the reusable machinery the bridge file (`Def_mme_tensor_bridge`) needs
to prove `MMq_cyclic`: a cyclic permutation of the three mode spaces of an order-3 tensor.

* `TensorObj.permObj σ X` — reindex the mode spaces `X.V` by `σ` (mode `i` of the result
  comes from mode `σ.symm i` of `X`) and transport the element via `PiTensorProduct.reindex`.
* `permObj_restrict` / `permObj_isomorphic` — `permObj σ` preserves `TensorObj.Restrict`
  (hence isomorphism), so it descends to the quotient.
* `permObj_MMObj` (here `MMObj_permObj_cyclic`) — for the 3-cycle `cyclicPerm`,
  `permObj cyclicPerm (MMObj n m p) ≅ MMObj p n m` (the cyclic shift of dimensions).
* `TensorQ.permAut σ` — the descended map on the quotient, bundled as a ring homomorphism
  `TensorQ K 3 →+* TensorQ K 3` (it respects `+ = add`, `* = kron`, `0`, `1`), together with
    - `permAut_le` : monotone for the restriction order `TensorQ.le`,
    - `permAut_MMq` : `permAut cyclicPerm (toQ (MMObj n m p)) = toQ (MMObj p n m)`.

Convention (matching `PiTensorProduct.reindex`): `(permObj σ X).V i = X.V (σ.symm i)` and
`(permObj σ X).t = reindex K X.V σ X.t`, where `reindex K s e : (⨂ i, s i) ≃ₗ ⨂ i, s (e.symm i)`. -/

universe u

open PiTensorProduct TensorProduct BigOperators

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-! ## `reindex` commutes with `interchange`

The Kronecker product is built from the mode-wise `interchange` map; transporting it under a
mode reindexing is the naturality fact `reindex (interchange a b) = interchange (reindex a)
(reindex b)`. -/

/-- `interchange` on pure tensors. (Re-derived locally since the quotient file's copy is
`private`.) -/
private theorem interchange_tprod_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- Reindexing commutes with the mode-wise `interchange` map. -/
theorem reindex_interchange {ι ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₂]
    [DecidableEq ι₂] {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (σ : ι ≃ ι₂) (t₁ : PiTensorProduct K V) (t₂ : PiTensorProduct K W) :
    (reindex K (fun i => V i ⊗[K] W i) σ) (interchange t₁ t₂) =
    interchange ((reindex K V σ) t₁) ((reindex K W σ) t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c₁ v₁ =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c₂ v₂ =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod_pure v₁ v₂,
          PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod,
          PiTensorProduct.reindex_tprod, interchange_tprod_pure]
    | add x y ihx ihy =>
      have hx : (reindex K (fun i => V i ⊗[K] W i) σ) (interchange (c₁ • tprod K v₁) x) =
          interchange ((reindex K V σ) (c₁ • tprod K v₁)) ((reindex K W σ) x) := ihx
      have hy : (reindex K (fun i => V i ⊗[K] W i) σ) (interchange (c₁ • tprod K v₁) y) =
          interchange ((reindex K V σ) (c₁ • tprod K v₁)) ((reindex K W σ) y) := ihy
      simp only [map_add, hx, hy]
  | add x y ihx ihy =>
    simp only [map_add, LinearMap.add_apply, ihx, ihy]

namespace TensorObj

/-! ## `permObj` on `TensorObj` -/

/-- Permute the mode spaces of a `TensorObj` by `σ : Equiv.Perm (Fin d)`. Mode `i` of the
result comes from mode `σ.symm i` of the input, matching `PiTensorProduct.reindex`. -/
@[reducible] noncomputable def permObj (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj K d where
  V i := X.V (σ.symm i)
  acg i := X.acg (σ.symm i)
  mod i := X.mod (σ.symm i)
  fin i := X.fin (σ.symm i)
  t := PiTensorProduct.reindex K X.V σ X.t

/-- `permObj σ` preserves `TensorObj.Restrict`. -/
theorem permObj_restrict (σ : Equiv.Perm (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (permObj σ X) (permObj σ Y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun i => f (σ.symm i), ?_⟩
  show PiTensorProduct.map (fun i => f (σ.symm i)) ((PiTensorProduct.reindex K Y.V σ) Y.t) =
      (PiTensorProduct.reindex K X.V σ) X.t
  rw [PiTensorProduct.map_reindex, hf]

/-- `permObj σ` preserves isomorphism (mutual restriction). -/
theorem permObj_isomorphic (σ : Equiv.Perm (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Isomorphic X Y) :
    TensorObj.Isomorphic (permObj σ X) (permObj σ Y) :=
  ⟨permObj_restrict σ h.1, permObj_restrict σ h.2⟩

/-! ## `permObj` is a homomorphism for `add`/`kron`/`zeroObj`/`oneObj` (up to isomorphism) -/

/-- `permObj σ (add X Y)` is isomorphic to `add (permObj σ X) (permObj σ Y)`. The mode spaces
agree on the nose (`X.V (σ.symm i) × Y.V (σ.symm i)`); the elements match because `reindex`
commutes with `inl`/`inr` via `PiTensorProduct.map_reindex`. -/
theorem permObj_add_iso (σ : Equiv.Perm (Fin d)) (X Y : TensorObj K d) :
    TensorObj.Isomorphic (permObj σ (TensorObj.add X Y))
      (TensorObj.add (permObj σ X) (permObj σ Y)) := by
  have key : (permObj σ (TensorObj.add X Y)).t = (TensorObj.add (permObj σ X) (permObj σ Y)).t := by
    show (PiTensorProduct.reindex K (fun i => X.V i × Y.V i) σ)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) =
        PiTensorProduct.map (fun i => LinearMap.inl K (X.V (σ.symm i)) (Y.V (σ.symm i)))
          ((PiTensorProduct.reindex K X.V σ) X.t) +
        PiTensorProduct.map (fun i => LinearMap.inr K (X.V (σ.symm i)) (Y.V (σ.symm i)))
          ((PiTensorProduct.reindex K Y.V σ) Y.t)
    rw [map_add,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inl K (X.V i) (Y.V i)) σ X.t,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inr K (X.V i) (Y.V i)) σ Y.t]
  refine ⟨⟨fun _ => LinearMap.id, ?_⟩, ⟨fun _ => LinearMap.id, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => LinearMap.id)
        (TensorObj.add (permObj σ X) (permObj σ Y)).t = (permObj σ (TensorObj.add X Y)).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, key]
  · show PiTensorProduct.map (fun _ => LinearMap.id)
        (permObj σ (TensorObj.add X Y)).t = (TensorObj.add (permObj σ X) (permObj σ Y)).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, key]

/-- `permObj σ (kron X Y)` is isomorphic to `kron (permObj σ X) (permObj σ Y)`, by
`reindex_interchange`. -/
theorem permObj_kron_iso (σ : Equiv.Perm (Fin d)) (X Y : TensorObj K d) :
    TensorObj.Isomorphic (permObj σ (TensorObj.kron X Y))
      (TensorObj.kron (permObj σ X) (permObj σ Y)) := by
  have key : (permObj σ (TensorObj.kron X Y)).t =
      (TensorObj.kron (permObj σ X) (permObj σ Y)).t := by
    show (PiTensorProduct.reindex K (fun i => X.V i ⊗[K] Y.V i) σ) (interchange X.t Y.t) =
        interchange ((PiTensorProduct.reindex K X.V σ) X.t) ((PiTensorProduct.reindex K Y.V σ) Y.t)
    exact reindex_interchange σ X.t Y.t
  refine ⟨⟨fun _ => LinearMap.id, ?_⟩, ⟨fun _ => LinearMap.id, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => LinearMap.id)
        (TensorObj.kron (permObj σ X) (permObj σ Y)).t = (permObj σ (TensorObj.kron X Y)).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, key]
  · show PiTensorProduct.map (fun _ => LinearMap.id)
        (permObj σ (TensorObj.kron X Y)).t = (TensorObj.kron (permObj σ X) (permObj σ Y)).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, key]

/-- `permObj σ zeroObj` is isomorphic to `zeroObj` (both have element `0`). -/
theorem permObj_zero_iso (σ : Equiv.Perm (Fin d)) :
    TensorObj.Isomorphic (permObj σ (TensorObj.zeroObj : TensorObj K d)) TensorObj.zeroObj := by
  have hzt : (TensorObj.zeroObj : TensorObj K d).t = 0 := rfl
  have hpt : (permObj σ (TensorObj.zeroObj : TensorObj K d)).t = 0 := by
    show (PiTensorProduct.reindex K (TensorObj.zeroObj : TensorObj K d).V σ)
        (TensorObj.zeroObj : TensorObj K d).t = 0
    rw [hzt, map_zero]
  refine ⟨⟨fun _ => 0, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (TensorObj.zeroObj : TensorObj K d).t =
        (permObj σ (TensorObj.zeroObj : TensorObj K d)).t
    rw [hzt, hpt, map_zero]
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _))
        (permObj σ (TensorObj.zeroObj : TensorObj K d)).t = (TensorObj.zeroObj : TensorObj K d).t
    rw [hpt, hzt, map_zero]

/-- `permObj σ oneObj` is isomorphic to `oneObj` (`reindex` fixes the all-`1` pure tensor). -/
theorem permObj_one_iso (σ : Equiv.Perm (Fin d)) :
    TensorObj.Isomorphic (permObj σ (TensorObj.oneObj : TensorObj K d)) TensorObj.oneObj := by
  have ht : (permObj σ (TensorObj.oneObj : TensorObj K d)).t = (TensorObj.oneObj : TensorObj K d).t := by
    show (PiTensorProduct.reindex K (fun _ : Fin d => K) σ)
        (tprod K (fun _ => (1 : K))) = tprod K (fun _ => (1 : K))
    rw [PiTensorProduct.reindex_tprod]
  refine ⟨⟨fun _ => LinearMap.id, ?_⟩, ⟨fun _ => LinearMap.id, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => LinearMap.id) (TensorObj.oneObj : TensorObj K d).t =
        (permObj σ (TensorObj.oneObj : TensorObj K d)).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, ht]
  · show PiTensorProduct.map (fun _ => LinearMap.id)
        (permObj σ (TensorObj.oneObj : TensorObj K d)).t = (TensorObj.oneObj : TensorObj K d).t
    rw [PiTensorProduct.map_id, LinearMap.id_coe, id_eq, ht]

end TensorObj

/-! ## The cyclic permutation of `Fin 3` and its action on `MMObj`

The three modes of `MM(n,m,p)` are the index spaces `(n×m), (m×p), (p×n)`. The 3-cycle
`0 → 1 → 2 → 0` permutes these so that the resulting object is (isomorphic to) `MM(p,n,m)`. -/

/-- The cyclic permutation of `Fin 3`: `0 ↦ 1 ↦ 2 ↦ 0`. Defined via explicit match so that
`cyclicPerm.symm` reduces definitionally on each case. -/
def cyclicPerm : Equiv.Perm (Fin 3) where
  toFun
    | ⟨0, _⟩ => ⟨1, by norm_num⟩
    | ⟨1, _⟩ => ⟨2, by norm_num⟩
    | ⟨2, _⟩ => ⟨0, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  invFun
    | ⟨0, _⟩ => ⟨2, by norm_num⟩
    | ⟨1, _⟩ => ⟨0, by norm_num⟩
    | ⟨2, _⟩ => ⟨1, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv := by decide
  right_inv := by decide

/-- Cyclic permutation of modes sends `MMObj n m p` to `MMObj p n m` (up to isomorphism via
the canonical mode-space identifications, which are identities). -/
theorem MMObj_permObj_cyclic (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj cyclicPerm (MMObj K n m p))
      (MMObj K p n m) := by
  -- After reindexing by cyclicPerm.symm, mode i of the result is mode (cyclicPerm.symm i):
  --   mode 0 ← MMSpace n m p 2 = Fin p × Fin n → K   →  MMObj p n m mode 0 = Fin p × Fin n → K
  --   mode 1 ← MMSpace n m p 0 = Fin n × Fin m → K   →  MMObj p n m mode 1 = Fin n × Fin m → K
  --   mode 2 ← MMSpace n m p 1 = Fin m × Fin p → K   →  MMObj p n m mode 2 = Fin m × Fin p → K
  -- so each mode space matches exactly; the bijection is the identity.
  let fwd : ∀ s : Fin 3,
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).V s →ₗ[K]
      (MMObj K p n m).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  let bwd : ∀ s : Fin 3,
      (MMObj K p n m).V s →ₗ[K]
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  -- `fwd` and `bwd` are mutually inverse componentwise (each is `LinearMap.id` at defeq types).
  have hcomp : (fun s => fwd s ∘ₗ bwd s) = fun s => (LinearMap.id : (MMObj K p n m).V s →ₗ[K] _) := by
    funext ⟨s, hs⟩
    match s, hs with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | s + 3, h => exact absurd h (by omega)
  -- The clean direction: `map bwd` applied to the *concrete* `MMTensor p n m` distributes fine.
  have hbwd_t : PiTensorProduct.map bwd (MMObj K p n m).t =
      (TensorObj.permObj cyclicPerm (MMObj K n m p)).t := by
    show PiTensorProduct.map bwd (MMTensor K p n m) =
        (PiTensorProduct.reindex K (MMSpace K n m p) cyclicPerm) (MMTensor K n m p)
    show PiTensorProduct.map bwd
        (∑ i : Fin p, ∑ j : Fin n, ∑ k : Fin m,
          tprod K (fun s => match s with
            | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin p × Fin n → K)
            | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin n × Fin m → K)
            | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin m × Fin p → K))) =
        (PiTensorProduct.reindex K (MMSpace K n m p) cyclicPerm)
          (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
            tprod K (fun s => match s with
              | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
              | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
              | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)))
    simp only [map_sum, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
    -- LHS sums over (I:Fin p, J:Fin n, K':Fin m); RHS over (i:Fin n, j:Fin m, k:Fin p).
    -- Match: I plays k, J plays i, K' plays j. Reorder LHS to (J, K', I) = (i, j, k).
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, J]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    congr 1
    ext ⟨s, hs⟩
    match s, hs with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | s + 3, h => exact absurd h (by omega)
  have hbwd : TensorObj.Restrict (TensorObj.permObj cyclicPerm (MMObj K n m p)) (MMObj K p n m) :=
    ⟨bwd, hbwd_t⟩
  -- The other direction: `map fwd` of the permuted element equals `MMTensor p n m`, derived
  -- from `hbwd_t` by composing with `bwd` (avoids distributing `map fwd` over a reindex-sum).
  have hfwd : TensorObj.Restrict (MMObj K p n m) (TensorObj.permObj cyclicPerm (MMObj K n m p)) := by
    refine ⟨fwd, ?_⟩
    show PiTensorProduct.map fwd (TensorObj.permObj cyclicPerm (MMObj K n m p)).t =
        (MMObj K p n m).t
    rw [← hbwd_t, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, hcomp,
        PiTensorProduct.map_id, LinearMap.id_coe, id_eq]
  exact ⟨hbwd, hfwd⟩

/-! ## Descent to the quotient `TensorQ` -/

namespace TensorQ

variable {K : Type u} [Field K] {d : ℕ}

/-- The mode permutation descended to the quotient `TensorQ K d`. -/
noncomputable def permQ (σ : Equiv.Perm (Fin d)) (x : TensorQ K d) : TensorQ K d :=
  Quotient.liftOn x (fun X => toQ (TensorObj.permObj σ X))
    (fun _ _ h => Quotient.sound (TensorObj.permObj_isomorphic σ h))

@[simp] theorem permQ_toQ (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    permQ σ (toQ X) = toQ (TensorObj.permObj σ X) := rfl

/-- `permQ σ` preserves addition (`= +` on the quotient). -/
theorem permQ_add (σ : Equiv.Perm (Fin d)) (x y : TensorQ K d) :
    permQ σ (x + y) = permQ σ x + permQ σ y := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  show toQ (TensorObj.permObj σ (TensorObj.add X Y)) =
      toQ (TensorObj.add (TensorObj.permObj σ X) (TensorObj.permObj σ Y))
  exact Quotient.sound (TensorObj.permObj_add_iso σ X Y)

/-- `permQ σ` preserves multiplication (`= *` on the quotient). -/
theorem permQ_mul (σ : Equiv.Perm (Fin d)) (x y : TensorQ K d) :
    permQ σ (x * y) = permQ σ x * permQ σ y := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  show toQ (TensorObj.permObj σ (TensorObj.kron X Y)) =
      toQ (TensorObj.kron (TensorObj.permObj σ X) (TensorObj.permObj σ Y))
  exact Quotient.sound (TensorObj.permObj_kron_iso σ X Y)

/-- `permQ σ` preserves zero. -/
theorem permQ_zero (σ : Equiv.Perm (Fin d)) : permQ σ (0 : TensorQ K d) = 0 :=
  Quotient.sound (TensorObj.permObj_zero_iso σ)

/-- `permQ σ` preserves one. -/
theorem permQ_one (σ : Equiv.Perm (Fin d)) : permQ σ (1 : TensorQ K d) = 1 :=
  Quotient.sound (TensorObj.permObj_one_iso σ)

/-- `permQ σ` bundled as a ring homomorphism `TensorQ K d →+* TensorQ K d`. This is the
`permAut` the bridge file uses to build a permuted spectrum point `φ' := φ ∘ permAut`. -/
noncomputable def permAut (σ : Equiv.Perm (Fin d)) : TensorQ K d →+* TensorQ K d where
  toFun := permQ σ
  map_one' := permQ_one σ
  map_mul' := permQ_mul σ
  map_zero' := permQ_zero σ
  map_add' := permQ_add σ

@[simp] theorem permAut_apply (σ : Equiv.Perm (Fin d)) (x : TensorQ K d) :
    permAut σ x = permQ σ x := rfl

@[simp] theorem permAut_toQ (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    permAut σ (toQ X) = toQ (TensorObj.permObj σ X) := rfl

/-- **Monotonicity.** `permAut σ` (equivalently `permQ σ`) is monotone for the restriction
order `TensorQ.le`, because `permObj σ` preserves `TensorObj.Restrict`. -/
theorem permAut_le (σ : Equiv.Perm (Fin d)) {x y : TensorQ K d} (h : TensorQ.le x y) :
    TensorQ.le (permAut σ x) (permAut σ y) := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  exact TensorObj.permObj_restrict σ h

end TensorQ

/-- **Cyclic symmetry of the MM tensors on the quotient.**
`permAut cyclicPerm (toQ (MMObj n m p)) = toQ (MMObj p n m)` — the realization of the cyclic
mode symmetry as a ring-automorphism identity. This is what the bridge needs for `MMq_cyclic`. -/
theorem permAut_MMq (n m p : ℕ) :
    TensorQ.permAut cyclicPerm (TensorQ.toQ (MMObj K n m p)) =
      TensorQ.toQ (MMObj K p n m) := by
  show TensorQ.toQ (TensorObj.permObj cyclicPerm (MMObj K n m p)) = TensorQ.toQ (MMObj K p n m)
  exact Quotient.sound (MMObj_permObj_cyclic n m p)

end MME


