-- Prove2me | Definitions.Def_mme_tensor_quotient
-- name    : mme_tensor_quotient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:36:57.611757+00:00
-- url     : https://prove2.me/theorems/8fc5da31-dc4e-4ace-869c-cce3dc918587
-- statement:
--   **The tensor quotient `TensorQ K d`, its `CommSemiring`, and its canonical Strassen preorder.**
--
--   Builds the *isomorphism quotient* of `TensorObj K d` and descends the algebraic structure onto it, so that the abstract `StrassenPreorder`/spectrum theory can be instantiated on tensors.
--
--   **The quotient.** `TensorObj.Restrict` is a preorder (`refl`, `trans` inline); `TensorObj.Isomorphic X Y` (defined as restriction in both directions) is the equivalence relation; `TensorQ K d = Quot Isomorphic` is the quotient; `toQ : TensorObj K d → TensorQ K d` is the projection.
--
--   **Algebra.** The semiring operations `add` (direct sum $\oplus$) and `mul` (Kronecker product $\otimes$) of `TensorObj` descend to `TensorQ` because they preserve isomorphism (`add_respects_iso`, `mul_respects_iso`); together with `zero_iso`, `one_iso`, and the **interchange naturality** `map_interchange` (essential for unitality and distributivity), this gives a `CommSemiring` structure on `TensorQ K d`.
--
--   **Strassen preorder.** `tensorStrassen : StrassenPreorder (TensorQ K 3)` is the canonical preorder on the quotient: its `le` is "restriction (in either direction) on the underlying tensors". The natural-number-order-embedding axiom is supplied by `Def_mme_flattening` (flattening rank of a diagonal equals its size).
--
--   **Status.** The full file is sorry-free in MME after the user's reshape. The `CommSemiring` axioms are proved by routing through standard tensor-algebra isomorphisms (`TensorProduct.assoc`, `TensorProduct.comm`, `lid`/`rid`), and the `Restrict`/`Isomorphic`/`tensorStrassen` instances are established on top.

import Mathlib.LinearAlgebra.TensorProduct.Prod
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_strassen_preorder
import Definitions.Def_mme_flattening

/-! # The tensor quotient `TensorQ`, its semiring/preorder, and bridges (MME)

Builds the isomorphism quotient `TensorQ K d` of `TensorObj K d`, descends the direct
sum (`+`) and Kronecker product (`*`), and packages the `CommSemiring` + abstract
`StrassenPreorder` (`tensorStrassen`) used to instantiate the asymptotic-spectrum theory.

The lightweight, sorry-free part:
* `TensorObj.Restrict` is a preorder (`Restrict.refl`, `Restrict.trans`);
* `Isomorphic` is an equivalence relation and the quotient `TensorQ` is formed;
* `toQ : TensorObj K d → TensorQ K d` and the `Zero`/`One`/`Add`/`Mul` instances.

The genuinely deep obligations are isolated as clearly-labelled `sorry` leaves
(`CommSemiring` laws via tensor-algebra isomorphisms; `tensorStrassen`'s
`nat_order_embedding` via flattening; the analytic bridges connecting the abstract
`rank`/`asymptoticRank`/`ω` to the concrete `tensorRankObj`/`tensorAsymptoticRank`/
`matMulExp_strassen`). Each `sorry` carries a doc comment stating what it needs. -/

universe u

open PiTensorProduct TensorProduct BigOperators

namespace MME

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ}

/-! ## `Restrict` is a preorder -/

/-- Reflexivity of restriction (`id` maps). -/
theorem Restrict.refl (X : TensorObj K d) : TensorObj.Restrict X X :=
  ⟨fun _ => LinearMap.id, by rw [PiTensorProduct.map_id]; rfl⟩

/-- Transitivity of restriction (compose the maps). -/
theorem Restrict.trans {X Y Z : TensorObj K d}
    (hXY : TensorObj.Restrict X Y) (hYZ : TensorObj.Restrict Y Z) :
    TensorObj.Restrict X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  refine ⟨fun i => f i ∘ₗ g i, ?_⟩
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hg, hf]

/-- Two tensor objects are isomorphic if each restricts to the other. -/
def Isomorphic (X Y : TensorObj K d) : Prop :=
  TensorObj.Restrict X Y ∧ TensorObj.Restrict Y X

theorem Isomorphic.refl (X : TensorObj K d) : Isomorphic X X :=
  ⟨Restrict.refl X, Restrict.refl X⟩

theorem Isomorphic.symm {X Y : TensorObj K d} (h : Isomorphic X Y) : Isomorphic Y X :=
  ⟨h.2, h.1⟩

theorem Isomorphic.trans {X Y Z : TensorObj K d}
    (hXY : Isomorphic X Y) (hYZ : Isomorphic Y Z) : Isomorphic X Z :=
  ⟨Restrict.trans hXY.1 hYZ.1, Restrict.trans hYZ.2 hXY.2⟩

/-- The isomorphism setoid on `TensorObj K d`. -/
instance tensorSetoid (K : Type u) [Field K] (d : ℕ) : Setoid (TensorObj K d) where
  r := Isomorphic
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

end TensorObj

/-- The quotient of `TensorObj` by isomorphism. Note `TensorObj K d : Type (u+1)`
(it bundles a family of `Type u` spaces), so the quotient also lives in `Type (u+1)`. -/
def TensorQ (K : Type u) [Field K] (d : ℕ) : Type (u + 1) :=
  Quotient (TensorObj.tensorSetoid K d)

namespace TensorQ

variable {K : Type u} [Field K] {d : ℕ}

/-- The class of a tensor object. -/
def toQ (X : TensorObj K d) : TensorQ K d := Quotient.mk (TensorObj.tensorSetoid K d) X

theorem toQ_eq_iff {X Y : TensorObj K d} :
    toQ X = toQ Y ↔ TensorObj.Isomorphic X Y :=
  Quotient.eq

/-! ## Algebraic operations descended to the quotient

`add`/`mul` are well-defined because `TensorObj.add`/`kron` respect isomorphism. We mark
those compatibility facts as deep leaves (they are the functoriality of `⊕`/`⊗` under
restriction). -/

/-- A componentwise restriction `f : X ← X'`, `g : Y ← Y'` induces a restriction
`X⊕Y ← X'⊕Y'` via `f ⊕ g` (matching `inl`/`inr`). -/
private theorem add_restrict_aux {X X' Y Y' : TensorObj K d}
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

/-- Direct sum respects isomorphism (functoriality of `⊕`). -/
theorem add_respects_iso {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Isomorphic X X') (hY : TensorObj.Isomorphic Y Y') :
    TensorObj.Isomorphic (TensorObj.add X Y) (TensorObj.add X' Y') :=
  ⟨add_restrict_aux hX.1 hY.1, add_restrict_aux hX.2 hY.2⟩

/-- `interchange` on pure tensors. -/
private theorem interchange_tprod {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- Naturality of `interchange`: `map (f ⊗ g) (interchange a b) = interchange (map f a)
(map g b)`. -/
private theorem map_interchange {ι : Type*} [Fintype ι] [DecidableEq ι]
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
      rw [interchange_tprod, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_tprod]
      simp only [TensorProduct.map_tmul]
    | add x y ih1 ih2 =>
      simp only [map_add, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

/-- A componentwise restriction induces a restriction of Kronecker products via `f ⊗ g`. -/
private theorem mul_restrict_aux {X X' Y Y' : TensorObj K d}
    (hf : TensorObj.Restrict X X') (hg : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨fun i => TensorProduct.map (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
      (interchange X'.t Y'.t) = interchange X.t Y.t
  rw [map_interchange, hf, hg]

/-- Kronecker product respects isomorphism (functoriality of `⊗`). -/
theorem mul_respects_iso {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Isomorphic X X') (hY : TensorObj.Isomorphic Y Y') :
    TensorObj.Isomorphic (TensorObj.kron X Y) (TensorObj.kron X' Y') :=
  ⟨mul_restrict_aux hX.1 hY.1, mul_restrict_aux hX.2 hY.2⟩

noncomputable instance : Zero (TensorQ K d) := ⟨toQ TensorObj.zeroObj⟩
noncomputable instance : One (TensorQ K d) := ⟨toQ TensorObj.oneObj⟩

noncomputable instance : Add (TensorQ K d) :=
  ⟨fun x y => Quotient.liftOn₂ x y (fun X Y => toQ (TensorObj.add X Y))
    (fun _ _ _ _ hX hY => Quotient.sound (add_respects_iso hX hY))⟩

noncomputable instance : Mul (TensorQ K d) :=
  ⟨fun x y => Quotient.liftOn₂ x y (fun X Y => toQ (TensorObj.kron X Y))
    (fun _ _ _ _ hX hY => Quotient.sound (mul_respects_iso hX hY))⟩

@[simp] theorem toQ_add (X Y : TensorObj K d) :
    toQ X + toQ Y = toQ (TensorObj.add X Y) := rfl
@[simp] theorem toQ_mul (X Y : TensorObj K d) :
    toQ X * toQ Y = toQ (TensorObj.kron X Y) := rfl
@[simp] theorem toQ_zero : (0 : TensorQ K d) = toQ TensorObj.zeroObj := rfl
@[simp] theorem toQ_one : (1 : TensorQ K d) = toQ TensorObj.oneObj := rfl

/-! ### Tractable semiring isomorphisms (sorry-free) -/

/-- `interchange` is commutative up to `TensorProduct.comm`. -/
private theorem interchange_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) :
    PiTensorProduct.map (fun i => (TensorProduct.comm K (W i) (V i)).toLinearMap)
      (interchange b a) = interchange a b := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [interchange_tprod, PiTensorProduct.map_tprod, interchange_tprod, mul_comm c c']
      congr 2
    | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 => simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- Direct sum is commutative up to isomorphism. -/
private theorem add_comm_iso (X Y : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.add X Y) (TensorObj.add Y X) := by
  have key : ∀ A B : TensorObj K d, TensorObj.Restrict (TensorObj.add A B) (TensorObj.add B A) := by
    intro A B
    refine ⟨fun i => (LinearEquiv.prodComm K (B.V i) (A.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (LinearEquiv.prodComm K (B.V i) (A.V i)).toLinearMap)
        (PiTensorProduct.map (fun i => LinearMap.inl K (B.V i) (A.V i)) B.t +
         PiTensorProduct.map (fun i => LinearMap.inr K (B.V i) (A.V i)) A.t) =
        PiTensorProduct.map (fun i => LinearMap.inl K (A.V i) (B.V i)) A.t +
        PiTensorProduct.map (fun i => LinearMap.inr K (A.V i) (B.V i)) B.t
    have h1 : (fun i => (LinearEquiv.prodComm K (B.V i) (A.V i)).toLinearMap ∘ₗ
                  LinearMap.inl K (B.V i) (A.V i)) =
              (fun i => LinearMap.inr K (A.V i) (B.V i)) := by
      funext i; ext x <;> simp
    have h2 : (fun i => (LinearEquiv.prodComm K (B.V i) (A.V i)).toLinearMap ∘ₗ
                  LinearMap.inr K (B.V i) (A.V i)) =
              (fun i => LinearMap.inl K (A.V i) (B.V i)) := by
      funext i; ext x <;> simp
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, h1, h2, add_comm]
  exact ⟨key X Y, key Y X⟩

/-- Kronecker product is commutative up to isomorphism. -/
private theorem mul_comm_iso (X Y : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron X Y) (TensorObj.kron Y X) := by
  have key : ∀ A B : TensorObj K d, TensorObj.Restrict (TensorObj.kron A B) (TensorObj.kron B A) := by
    intro A B
    refine ⟨fun i => (TensorProduct.comm K (B.V i) (A.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.comm K (B.V i) (A.V i)).toLinearMap)
        (interchange B.t A.t) = interchange A.t B.t
    exact interchange_comm A.t B.t
  exact ⟨key X Y, key Y X⟩

/-- `kron zeroObj X` and `zeroObj` are isomorphic (its tensor element is `0`). -/
private theorem zero_mul_iso (X : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron TensorObj.zeroObj X) TensorObj.zeroObj := by
  have hzt : (TensorObj.kron TensorObj.zeroObj X).t = 0 := by
    show interchange (TensorObj.zeroObj : TensorObj K d).t X.t = 0
    show interchange (0 : PiTensorProduct K (fun _ : Fin d => PUnit)) X.t = 0
    rw [map_zero]; rfl
  refine ⟨⟨fun _ => 0, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (TensorObj.zeroObj : TensorObj K d).t =
      (TensorObj.kron TensorObj.zeroObj X).t
    rw [hzt]
    show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (0 : _) = 0
    exact LinearMap.map_zero _
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (TensorObj.kron TensorObj.zeroObj X).t =
      (TensorObj.zeroObj : TensorObj K d).t
    rw [hzt, map_zero]; rfl

/-- `add zeroObj X` is isomorphic to `X` (the `PUnit × X.V ≅ X.V` unitor). -/
private theorem zero_add_iso (X : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.add TensorObj.zeroObj X) X := by
  refine ⟨⟨fun i => LinearMap.inr K PUnit (X.V i), ?_⟩,
          ⟨fun i => LinearMap.snd K PUnit (X.V i), ?_⟩⟩
  · -- Restrict (add zeroObj X) X: map inr X.t = (add zeroObj X).t
    show PiTensorProduct.map (fun i => LinearMap.inr K PUnit (X.V i)) X.t =
        PiTensorProduct.map (fun i => LinearMap.inl K PUnit (X.V i))
          (TensorObj.zeroObj : TensorObj K d).t +
        PiTensorProduct.map (fun i => LinearMap.inr K PUnit (X.V i)) X.t
    show _ = PiTensorProduct.map (fun i => LinearMap.inl K PUnit (X.V i))
          (0 : PiTensorProduct K (fun _ : Fin d => PUnit)) + _
    rw [map_zero, zero_add]
  · -- Restrict X (add zeroObj X): map snd (add zeroObj X).t = X.t
    show PiTensorProduct.map (fun i => LinearMap.snd K PUnit (X.V i))
        (PiTensorProduct.map (fun i => LinearMap.inl K PUnit (X.V i))
          (TensorObj.zeroObj : TensorObj K d).t +
         PiTensorProduct.map (fun i => LinearMap.inr K PUnit (X.V i)) X.t) = X.t
    show PiTensorProduct.map (fun i => LinearMap.snd K PUnit (X.V i))
        (PiTensorProduct.map (fun i => LinearMap.inl K PUnit (X.V i))
          (0 : PiTensorProduct K (fun _ : Fin d => PUnit)) + _) = X.t
    rw [map_zero, zero_add, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    rw [show (fun i => LinearMap.snd K PUnit (X.V i) ∘ₗ LinearMap.inr K PUnit (X.V i)) =
        fun i => (LinearMap.id : X.V i →ₗ[K] X.V i) from by funext i; ext x; rfl]
    rw [PiTensorProduct.map_id]; rfl

/-- `diagObj K d 0` (the empty diagonal) is isomorphic to `zeroObj` (both have `t = 0`). -/
private theorem diagObj_zero_iso :
    TensorObj.Isomorphic (TensorObj.diagObj K d 0) TensorObj.zeroObj := by
  have hd0 : (TensorObj.diagObj K d 0).t = 0 := by
    show (∑ j : Fin 0, tprod K (fun _ => (Pi.single j 1 : Fin 0 → K))) = 0
    rw [Fin.sum_univ_zero]
  refine ⟨⟨fun _ => 0, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (TensorObj.zeroObj : TensorObj K d).t =
      (TensorObj.diagObj K d 0).t
    rw [hd0]; exact LinearMap.map_zero _
  · show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (TensorObj.diagObj K d 0).t =
      (TensorObj.zeroObj : TensorObj K d).t
    rw [hd0]; show PiTensorProduct.map (fun _ => (0 : _ →ₗ[K] _)) (0 : _) = (0 : _)
    exact LinearMap.map_zero _

/-- A natural number as an element of the quotient (via `diagObj`). -/
noncomputable def natCast (n : ℕ) : TensorQ K d := toQ (TensorObj.diagObj K d n)

/-! ### Associators, distributors, unitors, and `natCast_succ` (sorry-free)

These are the remaining structural `CommSemiring` isomorphisms, all proved here by the
same `Quotient.sound`-of-`Isomorphic` strategy as the commutativity/zero laws above:
each direction of an `Isomorphic` is a componentwise `LinearEquiv` (direct-sum associator
`prodAssoc`, tensor associator `assoc`, distributor `prodRight`, left unitor `lid`, and the
`Fin (n+1) ≃ Fin n ⊕ *` splitter `snocEquiv`), and the tensor-element compatibility is
pushed through `PiTensorProduct.map_comp` / `map_interchange` / the `interchange`-induction
helpers `interchange_assoc`, `interchange_one`. -/

/-- Collapse a composite of two `PiTensorProduct.map`s into one (functoriality). -/
private theorem map_collapse {V₁ V₂ V₃ : Fin d → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    (f : ∀ i, V₂ i →ₗ[K] V₃ i) (g : ∀ i, V₁ i →ₗ[K] V₂ i) (t : PiTensorProduct K V₁) :
    PiTensorProduct.map f (PiTensorProduct.map g t) =
      PiTensorProduct.map (fun i => f i ∘ₗ g i) t := by
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]

/-- Direct sum is associative up to isomorphism (`prodAssoc` on mode spaces). -/
private theorem add_assoc_iso (X Y Z : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.add (TensorObj.add X Y) Z)
      (TensorObj.add X (TensorObj.add Y Z)) := by
  constructor
  · refine ⟨fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i × Z.V i)) X.t +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
           (PiTensorProduct.map (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t +
            PiTensorProduct.map (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t)) =
        PiTensorProduct.map (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
          (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
           PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) +
        PiTensorProduct.map (fun i => LinearMap.inr K (X.V i × Y.V i) (Z.V i)) Z.t
    have h1 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
                  LinearMap.inl K (X.V i) (Y.V i × Z.V i)) =
              (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    have h2 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
                  LinearMap.inr K (X.V i) (Y.V i × Z.V i) ∘ₗ LinearMap.inl K (Y.V i) (Z.V i)) =
              (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    have h3 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
                  LinearMap.inr K (X.V i) (Y.V i × Z.V i) ∘ₗ LinearMap.inr K (Y.V i) (Z.V i)) =
              (fun i => LinearMap.inr K (X.V i × Y.V i) (Z.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    simp only [map_add, map_collapse, h1, h2, h3, add_assoc]
  · refine ⟨fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
          (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
           PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V i × Y.V i) (Z.V i)) Z.t) =
        PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i × Z.V i)) X.t +
        PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
          (PiTensorProduct.map (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t +
           PiTensorProduct.map (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t)
    have g1 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap ∘ₗ
                  (LinearMap.inl K (X.V i × Y.V i) (Z.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i))) =
              (fun i => LinearMap.inl K (X.V i) (Y.V i × Z.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    have g2 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap ∘ₗ
                  (LinearMap.inl K (X.V i × Y.V i) (Z.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i))) =
              (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i) ∘ₗ LinearMap.inl K (Y.V i) (Z.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    have g3 : (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap ∘ₗ
                  LinearMap.inr K (X.V i × Y.V i) (Z.V i)) =
              (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i) ∘ₗ LinearMap.inr K (Y.V i) (Z.V i)) := by
      funext i; ext x <;> simp [LinearEquiv.prodAssoc]
    simp only [map_add, map_collapse, g1, g2, g3, add_assoc]

/-- Kronecker product distributes over direct sum on the right (`prodRight` distributor). -/
private theorem left_distrib_iso (X Y Z : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron X (TensorObj.add Y Z))
      (TensorObj.add (TensorObj.kron X Y) (TensorObj.kron X Z)) := by
  constructor
  · refine ⟨fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) (interchange X.t Y.t) +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) (interchange X.t Z.t)) =
        interchange X.t (PiTensorProduct.map (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t +
                         PiTensorProduct.map (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t)
    have c1 : (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
                  LinearMap.inl K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) =
              (fun i => TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inl K (Y.V i) (Z.V i))) := by
      funext i; apply TensorProduct.ext'; intro x y; simp only [LinearMap.comp_apply,
        LinearMap.inl_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe]
      rw [show (0 : X.V i ⊗[K] Z.V i) = x ⊗ₜ[K] (0:Z.V i) by rw [tmul_zero], prodRight_symm_tmul]
    have c2 : (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
                  LinearMap.inr K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) =
              (fun i => TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inr K (Y.V i) (Z.V i))) := by
      funext i; apply TensorProduct.ext'; intro x z; simp only [LinearMap.comp_apply,
        LinearMap.inr_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe]
      rw [show (0 : X.V i ⊗[K] Y.V i) = x ⊗ₜ[K] (0:Y.V i) by rw [tmul_zero], prodRight_symm_tmul]
    rw [map_add, map_collapse, map_collapse, c1, c2, map_interchange, map_interchange,
        PiTensorProduct.map_id, LinearMap.id_coe, id_eq, ← map_add]
  · refine ⟨fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (interchange X.t (PiTensorProduct.map (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t +
                          PiTensorProduct.map (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t)) =
        PiTensorProduct.map (fun i => LinearMap.inl K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) (interchange X.t Y.t) +
        PiTensorProduct.map (fun i => LinearMap.inr K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) (interchange X.t Z.t)
    have d1 : (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).toLinearMap ∘ₗ
                  TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inl K (Y.V i) (Z.V i))) =
              (fun i => LinearMap.inl K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) := by
      funext i; apply TensorProduct.ext'; intro x y; simp only [LinearMap.comp_apply,
        TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.inl_apply, LinearEquiv.coe_coe,
        prodRight_tmul, tmul_zero]
    have d2 : (fun i => (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).toLinearMap ∘ₗ
                  TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inr K (Y.V i) (Z.V i))) =
              (fun i => LinearMap.inr K (X.V i ⊗[K] Y.V i) (X.V i ⊗[K] Z.V i)) := by
      funext i; apply TensorProduct.ext'; intro x z; simp only [LinearMap.comp_apply,
        TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.inr_apply, LinearEquiv.coe_coe,
        prodRight_tmul, tmul_zero]
    rw [map_add]
    rw [show interchange X.t (PiTensorProduct.map (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t) =
          PiTensorProduct.map (fun i => TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inl K (Y.V i) (Z.V i))) (interchange X.t Y.t) by
      rw [map_interchange, PiTensorProduct.map_id, LinearMap.id_coe, id_eq]]
    rw [show interchange X.t (PiTensorProduct.map (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t) =
          PiTensorProduct.map (fun i => TensorProduct.map (LinearMap.id : X.V i →ₗ[K] X.V i) (LinearMap.inr K (Y.V i) (Z.V i))) (interchange X.t Z.t) by
      rw [map_interchange, PiTensorProduct.map_id, LinearMap.id_coe, id_eq]]
    rw [map_add, map_collapse, map_collapse, d1, d2]

/-- The right distributor, obtained from `left_distrib_iso` by commutativity. -/
private theorem right_distrib_iso (X Y Z : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron (TensorObj.add X Y) Z)
      (TensorObj.add (TensorObj.kron X Z) (TensorObj.kron Y Z)) :=
  (mul_comm_iso (TensorObj.add X Y) Z).trans
    ((left_distrib_iso Z X Y).trans
      (add_respects_iso (mul_comm_iso Z X) (mul_comm_iso Z Y)))

/-- `interchange` is associative up to `TensorProduct.assoc` (mode-wise). -/
private theorem interchange_assoc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) (c : PiTensorProduct K U) :
    PiTensorProduct.map (fun i => (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap)
      (interchange (interchange a b) c) = interchange a (interchange b c) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [interchange_tprod, interchange_tprod, PiTensorProduct.map_tprod,
            interchange_tprod, interchange_tprod, show cc * (cb * ca) = cc * cb * ca from by ring]
        congr 1
      | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 => simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- Kronecker product is associative up to isomorphism (`assoc` on mode spaces). -/
private theorem mul_assoc_iso (X Y Z : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron (TensorObj.kron X Y) Z)
      (TensorObj.kron X (TensorObj.kron Y Z)) := by
  constructor
  · refine ⟨fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (interchange X.t (interchange Y.t Z.t)) = interchange (interchange X.t Y.t) Z.t
    rw [← interchange_assoc X.t Y.t Z.t, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
        show (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
              (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap) =
            (fun i => (LinearMap.id : ((X.V i ⊗[K] Y.V i) ⊗[K] Z.V i) →ₗ[K] _)) from by
          funext i; ext t; simp,
        PiTensorProduct.map_id]
    rfl
  · refine ⟨fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (interchange (interchange X.t Y.t) Z.t) = interchange X.t (interchange Y.t Z.t)
    exact interchange_assoc X.t Y.t Z.t

/-- `map lid (interchange (1⊗⋯⊗1) a) = a` (the left tensor unitor on the element). -/
private theorem interchange_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (a : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => (TensorProduct.lid K (V i)).toLinearMap)
      (interchange (tprod K (fun _ => (1:K))) a) = a := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    rw [interchange_tprod, PiTensorProduct.map_tprod]
    simp only [LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]
  | add x y ih1 ih2 => simp only [map_add, ih1, ih2]

/-- `oneObj` is a left unit for the Kronecker product up to isomorphism (`lid` unitor). -/
private theorem one_mul_iso (X : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron TensorObj.oneObj X) X := by
  have hone : (TensorObj.kron TensorObj.oneObj X).t =
      interchange (tprod K (fun _ : Fin d => (1:K))) X.t := rfl
  constructor
  · refine ⟨fun i => (TensorProduct.lid K (X.V i)).symm.toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.lid K (X.V i)).symm.toLinearMap) X.t =
        (TensorObj.kron TensorObj.oneObj X).t
    rw [hone]
    have key : PiTensorProduct.map (fun i => (TensorProduct.lid K (X.V i)).symm.toLinearMap)
        (PiTensorProduct.map (fun i => (TensorProduct.lid K (X.V i)).toLinearMap)
          (interchange (tprod K (fun _ : Fin d => (1:K))) X.t)) =
        interchange (tprod K (fun _ : Fin d => (1:K))) X.t := by
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
          show (fun i => (TensorProduct.lid K (X.V i)).symm.toLinearMap ∘ₗ
                (TensorProduct.lid K (X.V i)).toLinearMap) =
              (fun i => (LinearMap.id : (K ⊗[K] X.V i) →ₗ[K] _)) from by
            funext i; ext t; simp,
          PiTensorProduct.map_id]
      rfl
    rw [interchange_one X.t] at key
    exact key
  · refine ⟨fun i => (TensorProduct.lid K (X.V i)).toLinearMap, ?_⟩
    show PiTensorProduct.map (fun i => (TensorProduct.lid K (X.V i)).toLinearMap)
        (TensorObj.kron TensorObj.oneObj X).t = X.t
    rw [hone]
    exact interchange_one X.t

/-- `oneObj` is a right unit (from `one_mul_iso` via commutativity). -/
private theorem mul_one_iso (X : TensorObj K d) :
    TensorObj.Isomorphic (TensorObj.kron X TensorObj.oneObj) X :=
  (mul_comm_iso X TensorObj.oneObj).trans (one_mul_iso X)

/-- The mode-wise splitter `(Fin (n+1) → K) ≃ₗ (Fin n → K) × K` (peel off the last coord). -/
noncomputable def snocEquiv (K : Type u) [Field K] (n : ℕ) :
    (Fin (n+1) → K) ≃ₗ[K] (Fin n → K) × K where
  toFun v := (fun j => v j.castSucc, v (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  map_add' a b := by ext <;> simp
  map_smul' c a := by ext <;> simp
  left_inv v := by
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp
    · intro i; simp
  right_inv p := by
    ext
    · simp
    · simp

private theorem snocEquiv_single_last (n : ℕ) :
    snocEquiv K n (Pi.single (Fin.last n) 1) = (0, 1) := by
  apply Prod.ext
  · funext j
    show (Pi.single (Fin.last n) (1:K) : Fin (n+1) → K) j.castSucc = (0:Fin n → K) j
    rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]; rfl
  · show (Pi.single (Fin.last n) (1:K) : Fin (n+1) → K) (Fin.last n) = (1:K)
    rw [Pi.single_eq_same]

private theorem snocEquiv_single_castSucc (n : ℕ) (j : Fin n) :
    snocEquiv K n (Pi.single j.castSucc 1) = (Pi.single j 1, 0) := by
  apply Prod.ext
  · funext k
    show (Pi.single j.castSucc (1:K) : Fin (n+1) → K) k.castSucc = (Pi.single j (1:K) : Fin n → K) k
    by_cases h : k = j
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun hc => h (Fin.castSucc_injective n hc))]
  · show (Pi.single j.castSucc (1:K) : Fin (n+1) → K) (Fin.last n) = (0:K)
    rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne']

/-- `map snocEquiv` carries `diagObj (n+1)` to `(diagObj n) ⊕ oneObj`. -/
private theorem map_snocEquiv_diag (n : ℕ) :
    PiTensorProduct.map (fun _ : Fin d => (snocEquiv K n).toLinearMap)
      (TensorObj.diagObj K d (n+1)).t = (TensorObj.add (TensorObj.diagObj K d n) TensorObj.oneObj).t := by
  show PiTensorProduct.map (fun _ : Fin d => (snocEquiv K n).toLinearMap)
      (∑ j : Fin (n+1), tprod K (fun _ : Fin d => (Pi.single j 1 : Fin (n+1) → K))) =
      PiTensorProduct.map (fun i => LinearMap.inl K (Fin n → K) K)
        (∑ j : Fin n, tprod K (fun _ : Fin d => (Pi.single j 1 : Fin n → K))) +
      PiTensorProduct.map (fun i => LinearMap.inr K (Fin n → K) K)
        (tprod K (fun _ : Fin d => (1:K)))
  rw [Fin.sum_univ_castSucc, map_add, map_sum, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    rw [LinearEquiv.coe_coe, snocEquiv_single_castSucc]
    rfl
  · rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    rw [LinearEquiv.coe_coe, snocEquiv_single_last]
    rfl

/-- `diagObj (n+1) ≅ diagObj n ⊕ oneObj`, the `natCast (n+1) = natCast n + 1` law. -/
private theorem natCast_succ_iso (n : ℕ) :
    TensorObj.Isomorphic (TensorObj.diagObj K d (n+1))
      (TensorObj.add (TensorObj.diagObj K d n) TensorObj.oneObj) := by
  constructor
  · refine ⟨fun _ : Fin d => (snocEquiv K n).symm.toLinearMap, ?_⟩
    show PiTensorProduct.map (fun _ : Fin d => (snocEquiv K n).symm.toLinearMap)
        (TensorObj.add (TensorObj.diagObj K d n) TensorObj.oneObj).t =
        (TensorObj.diagObj K d (n+1)).t
    rw [← map_snocEquiv_diag (d := d) n]
    erw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
        show (fun _ : Fin d => (snocEquiv K n).symm.toLinearMap ∘ₗ (snocEquiv K n).toLinearMap) =
            (fun _ : Fin d => (LinearMap.id : (Fin (n+1) → K) →ₗ[K] _)) from by
          funext i; ext t; simp,
        PiTensorProduct.map_id]
    rfl
  · refine ⟨fun _ : Fin d => (snocEquiv K n).toLinearMap, ?_⟩
    exact map_snocEquiv_diag (d := d) n

/-- **CommSemiring on the tensor quotient**. The carrier operations are the standalone
`Add`/`Mul`/`Zero`/`One` instances above (so their `Zero`/`One` are defeq to
`instZero`/`instOne`). The commutativity/zero laws (`add_comm`, `mul_comm`, `zero_add`,
`add_zero`, `zero_mul`, `mul_zero`) are proved sorry-free above (via `add_comm_iso`,
`mul_comm_iso`, `zero_add_iso`, `zero_mul_iso`). The remaining structural laws
(`add_assoc`, `left/right_distrib`, `mul_assoc`, `one_mul`, `mul_one`, `natCast_*`) are
the documented deep leaf: they hold via the associators/distributors/unitors of the Prism
`Tensor.lean` (`add_assoc_isomorphic`, `mul_add_isomorphic`, `mul_assoc_isomorphic`,
`one_mul_isomorphic`, ~300 LOC of explicit tensor isomorphisms). -/
noncomputable instance instCommSemiring : CommSemiring (TensorQ K d) where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  one := 1
  natCast := natCast
  add_assoc := by
    intro x y z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact Quotient.sound (add_assoc_iso X Y Z)
  zero_add := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact Quotient.sound (zero_add_iso X)
  add_zero := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    show toQ (TensorObj.add X TensorObj.zeroObj) = toQ X
    exact Quotient.sound
      ((add_comm_iso X TensorObj.zeroObj).trans (zero_add_iso X))
  add_comm := by
    intro x y
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    exact Quotient.sound (add_comm_iso X Y)
  left_distrib := by
    intro x y z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact Quotient.sound (left_distrib_iso X Y Z)
  right_distrib := by
    intro x y z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact Quotient.sound (right_distrib_iso X Y Z)
  zero_mul := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact Quotient.sound (zero_mul_iso X)
  mul_zero := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    show toQ (TensorObj.kron X TensorObj.zeroObj) = (0 : TensorQ K d)
    exact Quotient.sound
      ((mul_comm_iso X TensorObj.zeroObj).trans (zero_mul_iso X))
  mul_assoc := by
    intro x y z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact Quotient.sound (mul_assoc_iso X Y Z)
  one_mul := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact Quotient.sound (one_mul_iso X)
  mul_one := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact Quotient.sound (mul_one_iso X)
  mul_comm := by
    intro x y
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    exact Quotient.sound (mul_comm_iso X Y)
  nsmul := nsmulRec
  natCast_zero := Quotient.sound diagObj_zero_iso
  natCast_succ := by
    intro n
    exact Quotient.sound (natCast_succ_iso n)

end TensorQ

/-! ## The abstract Strassen preorder on the tensor quotient -/

namespace TensorQ

variable {K : Type u} [Field K] {d : ℕ}

/-- The restriction preorder descended to the quotient: `toQ X ≤ toQ Y ↔ Restrict X Y`. -/
def le (x y : TensorQ K d) : Prop :=
  Quotient.liftOn₂ x y (fun X Y => TensorObj.Restrict X Y)
    (fun _ _ _ _ hX hY => propext ⟨
      fun h => TensorObj.Restrict.trans hX.2 (TensorObj.Restrict.trans h hY.1),
      fun h => TensorObj.Restrict.trans hX.1 (TensorObj.Restrict.trans h hY.2)⟩)

@[simp] theorem le_toQ (X Y : TensorObj K d) :
    le (toQ X) (toQ Y) ↔ TensorObj.Restrict X Y := Iff.rfl

theorem le_refl (x : TensorQ K d) : le x x := by
  induction x using Quotient.inductionOn with | _ X => exact TensorObj.Restrict.refl X

theorem le_trans (x y z : TensorQ K d) : le x y → le y z → le x z := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  induction z using Quotient.inductionOn with | _ Z =>
  exact TensorObj.Restrict.trans

/-! ### Helper lemmas for the Strassen-preorder fields

The `add_right`/`mul_right`/`zero_le` laws are functoriality of `⊕`/`⊗` (reusing
`add_restrict_aux`/`mul_restrict_aux` with a reflexive restriction on the second factor).
The Archimedean fields require genuine tensor-algebra content (separating product
functionals for `lower_archimedean`, a finite basis decomposition for `upper_archimedean`),
and `nat_order_embedding` is the flattening lower bound `diag_restrict_iff`. -/

/-- `zeroObj` restricts to any `X` (the family of zero maps, killing every pure tensor since
`d ≥ 1`). -/
private theorem restrict_zeroObj_le (hd : 1 < d) (X : TensorObj K d) :
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

/-- If `X.t = 0` then `toQ X = 0` (an isomorphism to `zeroObj`, both with `t = 0`). -/
private theorem toQ_eq_zero_of_t_eq_zero (hd : 1 < d) {X : TensorObj K d} (hX : X.t = 0) :
    toQ X = (0 : TensorQ K d) := by
  apply Quotient.sound
  refine ⟨⟨fun _ => 0, ?_⟩, restrict_zeroObj_le hd X⟩
  show PiTensorProduct.map (fun _ => (0 : (TensorObj.zeroObj : TensorObj K d).V _ →ₗ[K] X.V _))
      (TensorObj.zeroObj : TensorObj K d).t = X.t
  show PiTensorProduct.map _ (0 : PiTensorProduct K (fun _ : Fin d => PUnit)) = X.t
  rw [map_zero, hX]

/-- The product functional `⨂ᵢ (b i).coord (p i)` applied to `X.t`, computed through
`constantBaseRingEquiv`, recovers the `p`-coordinate `(Basis.piTensorProduct b).repr X.t p`. -/
private theorem cbre_map_coord {X : TensorObj K d}
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

/-- If `X.t ≠ 0` then `oneObj` restricts to `X`: pick a product functional `⨂ᵢ φᵢ`
nonzero on `X.t` (it separates points since `X.t` has a nonzero basis coordinate), scale it
at one mode to take the value `1`, giving `map φ X.t = tprod (fun _ => 1) = oneObj.t`. -/
private theorem restrict_oneObj_le_of_t_ne_zero (hd : 1 < d) {X : TensorObj K d}
    (hX : X.t ≠ 0) : TensorObj.Restrict TensorObj.oneObj X := by
  have h0d : 0 < d := by omega
  let i₀ : Fin d := ⟨0, h0d⟩
  let κ : Fin d → Type u := fun i => Module.Free.ChooseBasisIndex K (X.V i)
  let b : ∀ i, Module.Basis (κ i) K (X.V i) := fun i => Module.Free.chooseBasis K (X.V i)
  let B := Basis.piTensorProduct b
  -- a nonzero basis coordinate of `X.t`
  have hne : B.repr X.t ≠ 0 := fun h => hX (by
    have := B.sum_repr X.t; rw [h] at this; simpa using this.symm)
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hne
  rw [Finsupp.coe_zero, Pi.zero_apply] at hp
  set c := B.repr X.t p with hc
  let g₀ : ∀ i, X.V i →ₗ[K] K := fun i => (b i).coord (p i)
  let g : ∀ i, X.V i →ₗ[K] K := Function.update g₀ i₀ (c⁻¹ • g₀ i₀)
  refine ⟨g, ?_⟩
  show PiTensorProduct.map g X.t = (TensorObj.oneObj : TensorObj K d).t
  -- scaling one factor of `map` scales the whole map
  have hmap : PiTensorProduct.map g X.t = c⁻¹ • PiTensorProduct.map g₀ X.t := by
    have := PiTensorProduct.map_update_smul (f := g₀) i₀ c⁻¹ (g₀ i₀)
    rw [Function.update_eq_self] at this
    rw [show g = Function.update g₀ i₀ (c⁻¹ • g₀ i₀) from rfl, this, LinearMap.smul_apply]
  have hc0 : (constantBaseRingEquiv (Fin d) K) (PiTensorProduct.map g₀ X.t) = c :=
    cbre_map_coord b p
  have hval : (constantBaseRingEquiv (Fin d) K) (PiTensorProduct.map g X.t) = 1 := by
    rw [hmap, map_smul, hc0, smul_eq_mul, inv_mul_cancel₀ hp]
  have hone : (constantBaseRingEquiv (Fin d) K) (TensorObj.oneObj : TensorObj K d).t = 1 := by
    show (constantBaseRingEquiv (Fin d) K) (tprod K (fun _ : Fin d => (1 : K))) = 1
    rw [constantBaseRingEquiv_tprod]; simp
  exact (constantBaseRingEquiv (Fin d) K).injective (hval.trans hone.symm)

/-- If `X.t` decomposes as a sum of `N` pure tensors then `X` restricts to `diagObj K d N`
(the basis-to-`g` map `∑ⱼ smulRight (proj j) (w j i)`). -/
private theorem restrict_diagObj_of_tprod_sum {X : TensorObj K d} {N : ℕ}
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

/-- Every `X` restricts to some diagonal `diagObj K d N`: write `X.t` in a tensor basis,
absorbing each coefficient into one mode to turn the basis expansion into a finite sum of
`N = ∏ᵢ dim(X.V i)` pure tensors. -/
private theorem exists_restrict_diagObj (hd : 1 < d) (X : TensorObj K d) :
    ∃ N : ℕ, TensorObj.Restrict X (TensorObj.diagObj K d N) := by
  have h0d : 0 < d := by omega
  let i₀ : Fin d := ⟨0, h0d⟩
  let κ : Fin d → Type u := fun i => Module.Free.ChooseBasisIndex K (X.V i)
  let b : ∀ i, Module.Basis (κ i) K (X.V i) := fun i => Module.Free.chooseBasis K (X.V i)
  let B := Basis.piTensorProduct b
  haveI : Fintype (∀ i, κ i) := inferInstance
  let r := Fintype.card (∀ i, κ i)
  let e : (∀ i, κ i) ≃ Fin r := Fintype.equivFin _
  -- pure tensor with the basis coefficient absorbed into mode `i₀`
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
  exact ⟨r, restrict_diagObj_of_tprod_sum v hsum⟩

/-- **The abstract Strassen preorder on `TensorQ K d` for `1 < d`.**

`le := Restrict`-descended. `add_right`/`mul_right` are functoriality of `⊕`/`⊗`
(`add_restrict_aux`/`mul_restrict_aux` with `Restrict.refl` on the unchanged factor);
`zero_le` is `restrict_zeroObj_le`. `nat_order_embedding` is the flattening lower bound
(`diag_restrict_iff`, since `(n : TensorQ) = toQ (diagObj n)`). `lower_archimedean` separates
`X.t = 0` (then `toQ X = 0`) from `X.t ≠ 0` (then `oneObj ≤ X` via a product functional);
`upper_archimedean` writes `X.t` as a finite sum of pure tensors (`exists_restrict_diagObj`). -/
noncomputable def tensorStrassen (K : Type u) [Field K] (d : ℕ) (hd : 1 < d) :
    StrassenPreorder (TensorQ K d) where
  toPreorder :=
    { le := le
      le_refl := le_refl
      le_trans := le_trans }
  add_right := by
    intro x y h z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact add_restrict_aux h (TensorObj.Restrict.refl Z)
  mul_right := by
    intro x y h z
    induction x using Quotient.inductionOn with | _ X =>
    induction y using Quotient.inductionOn with | _ Y =>
    induction z using Quotient.inductionOn with | _ Z =>
    exact mul_restrict_aux h (TensorObj.Restrict.refl Z)
  zero_le := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    exact restrict_zeroObj_le hd X
  nat_order_embedding := by
    intro n m
    show le (toQ (TensorObj.diagObj K d n)) (toQ (TensorObj.diagObj K d m)) ↔ n ≤ m
    rw [le_toQ]
    exact diag_restrict_iff hd n m
  lower_archimedean := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    by_cases hX : X.t = 0
    · left; exact toQ_eq_zero_of_t_eq_zero hd hX
    · right; exact restrict_oneObj_le_of_t_ne_zero hd hX
  upper_archimedean := by
    intro x
    induction x using Quotient.inductionOn with | _ X =>
    obtain ⟨N, hN⟩ := exists_restrict_diagObj hd X
    exact ⟨N, hN⟩

end TensorQ

end MME


