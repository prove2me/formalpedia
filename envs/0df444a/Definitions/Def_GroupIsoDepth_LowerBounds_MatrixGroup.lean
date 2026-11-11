-- Prove2me | Definitions.Def_GroupIsoDepth_LowerBounds_MatrixGroup
-- name    : GroupIsoDepth_LowerBounds_MatrixGroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:15.479681+00:00
-- url     : https://prove2.me/theorems/de5f45a2-f9d2-477f-a633-f7f3f2f90f18
-- title:
--   Construction 5.4: the group $G_M$ of a matrix $M\in\mathrm{Mat}_k(\mathbb F_2)$, its labelled Cayley table, and $I_r\oplus 0_{k-r}$
-- statement:
--   Given $M\in\mathrm{Mat}_k(\mathbb F_2)$, the elements of $G_M$ are pairs $(u,z)\in\mathbb F_2^k\times\mathbb F_2^k$ (so $|G_M|=2^{2k}$) with multiplication
--   $$(u,z)\cdot_M(v,w)=\big(u+v,\;z+w+M(u\odot v)\big),$$
--   where $(u\odot v)_i=u_iv_i$. The identity is $(0,0)$ and $(u,z)^{-1}=(-u,-z+M(u\odot u))$; this makes $G_M$ an abelian group.
--
--   The element $(u,z)$ has label $\sum_i u_i2^i+\sum_j z_j2^{k+j}\in[2^{2k}]$. The **Cayley table of $G_M$** is the table of order $n=4^k$ whose entry $(a,a')$ is the label of the product of the elements labelled $a$ and $a'$, written with $2k=\lceil\log_2 n\rceil$ bits. The **pair** $(G_M,G_N)$ is the Group Isomorphism instance made of the tables of $G_M$ and $G_N$. $I_r\oplus0_{k-r}$ is the $k\times k$ diagonal matrix $\mathrm{diag}(1,\dots,1,0,\dots,0)$ with $r$ ones.
--
--   **Formalization Note** `GM M` is a type synonym of `(Fin k → ZMod 2) × (Fin k → ZMod 2)` with its own `CommGroup` instance (proved, no sorry); `u ⊙ v` is the pointwise product `u * v`. The labelling is not fixed by the paper ("our chosen way of representing elements", p. 38); this one makes bit $i<k$ of a label equal $u_i$ and bit $k+j$ equal $z_j$.
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Construction 5.4 and the matrix I_r ⊕ 0_{k−r} (p. 37, PDF 38)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

/-! Grochow, Kardeş, Levet, *Group Isomorphism: Depth-2½ Circuits and Lower Bounds*, STOC 2027
submission (manuscript sha256 cd6cacd4…), Construction 5.4 and the matrix `I_r ⊕ 0_{k−r}`
(printed p. 37, PDF 38).

For `M ∈ Mat_k(𝔽₂)` the group `G_M` has elements `(u, z) ∈ 𝔽₂^k × 𝔽₂^k` and product
`(u, z) ·_M (v, w) = (u + v, z + w + M(u ⊙ v))`, where `u ⊙ v` is the coordinate-wise product
(`u * v` on `Fin k → ZMod 2`). Its Cayley table is written with the labelling
`label(u, z) = Σ_i u_i 2^i + Σ_j z_j 2^{k+j} ∈ [2^{2k}]`: bit `i < k` of a label is `u_i`, bit
`k + j` is `z_j`. -/

/-- The underlying type of `G_M` (Construction 5.4): pairs `(u, z) ∈ 𝔽₂^k × 𝔽₂^k`. -/
def GM {k : ℕ} (_M : Matrix (Fin k) (Fin k) (ZMod 2)) : Type :=
  (Fin k → ZMod 2) × (Fin k → ZMod 2)

namespace GM

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) (ZMod 2)}

/-- The element `(u, z)` of `G_M`. -/
def mk (M : Matrix (Fin k) (Fin k) (ZMod 2)) (u z : Fin k → ZMod 2) : GM M := (u, z)

/-- The first coordinate `u` of `(u, z) ∈ G_M`. -/
def u (g : GM M) : Fin k → ZMod 2 := Prod.fst g

/-- The second coordinate `z` of `(u, z) ∈ G_M`. -/
def z (g : GM M) : Fin k → ZMod 2 := Prod.snd g

@[ext] theorem ext {g h : GM M} (h₁ : g.u = h.u) (h₂ : g.z = h.z) : g = h :=
  Prod.ext h₁ h₂

@[simp] theorem u_mk (u z : Fin k → ZMod 2) : (mk M u z).u = u := rfl
@[simp] theorem z_mk (u z : Fin k → ZMod 2) : (mk M u z).z = z := rfl

instance : Fintype (GM M) := inferInstanceAs (Fintype ((Fin k → ZMod 2) × (Fin k → ZMod 2)))
instance : DecidableEq (GM M) :=
  inferInstanceAs (DecidableEq ((Fin k → ZMod 2) × (Fin k → ZMod 2)))

/-- The product of Construction 5.4: `(u, z) ·_M (v, w) = (u + v, z + w + M(u ⊙ v))`. -/
instance : Mul (GM M) := ⟨fun g h => mk M (g.u + h.u) (g.z + h.z + M.mulVec (g.u * h.u))⟩

/-- The identity `(0, 0)`. -/
instance : One (GM M) := ⟨mk M 0 0⟩

/-- The inverse `(u, z)⁻¹ = (−u, −z + M(u ⊙ u))`. -/
instance : Inv (GM M) := ⟨fun g => mk M (-g.u) (-g.z + M.mulVec (g.u * g.u))⟩

@[simp] theorem mul_u (g h : GM M) : (g * h).u = g.u + h.u := rfl
@[simp] theorem mul_z (g h : GM M) : (g * h).z = g.z + h.z + M.mulVec (g.u * h.u) := rfl
@[simp] theorem one_u : (1 : GM M).u = 0 := rfl
@[simp] theorem one_z : (1 : GM M).z = 0 := rfl
@[simp] theorem inv_u (g : GM M) : g⁻¹.u = -g.u := rfl
@[simp] theorem inv_z (g : GM M) : g⁻¹.z = -g.z + M.mulVec (g.u * g.u) := rfl

/-- `G_M` is an abelian group under the product of Construction 5.4. -/
instance : CommGroup (GM M) where
  mul_assoc a b c := by
    ext i <;> simp [Matrix.mulVec_add, add_mul, mul_add] <;> abel
  one_mul a := by ext i <;> simp
  mul_one a := by ext i <;> simp
  inv_mul_cancel a := by
    ext i <;> simp [Matrix.mulVec_neg, neg_mul, CharTwo.add_self_eq_zero]
  mul_comm a b := by
    ext i <;> simp [mul_comm, add_comm]

/-- The label of `(u, z)`: `Σ_i u_i 2^i + Σ_j z_j 2^{k+j}`, a number in `[2^{2k}]`. -/
def label (g : GM M) : ℕ :=
  (∑ i : Fin k, (g.u i).val * 2 ^ (i : ℕ)) + ∑ j : Fin k, (g.z j).val * 2 ^ (k + (j : ℕ))

/-- The element of `G_M` with label `a`: `u_i` is bit `i` of `a`, `z_j` is bit `k + j`. -/
def ofLabel (M : Matrix (Fin k) (Fin k) (ZMod 2)) (a : ℕ) : GM M :=
  mk M (fun i => if a.testBit i then 1 else 0) (fun j => if a.testBit (k + j) then 1 else 0)

end GM

/-- The labelled Cayley table of `G_M`, as the `N = n²⌈log₂ n⌉` input bits of a table of order
`n = 4^k = 2^{2k}`: bit `b` of entry `(a, a')` is bit `b` of `label(ofLabel a · ofLabel a')`. -/
def cayleyBits {k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod 2)) : TableVar (4 ^ k) → Bool :=
  fun v => (GM.label (GM.ofLabel M v.1 * GM.ofLabel M v.2.1)).testBit v.2.2

/-- The pair of tables `(G_M, G_N)` as the `2N` input bits of a Group Isomorphism instance. -/
def pairBits {k : ℕ} (M N : Matrix (Fin k) (Fin k) (ZMod 2)) : PairVar (4 ^ k) → Bool :=
  fun v => if v.1 = 0 then cayleyBits M v.2 else cayleyBits N v.2

/-- `I_r ⊕ 0_{k−r}`: the `k × k` diagonal matrix `diag(1, …, 1, 0, …, 0)` with `r` ones. -/
def Ir0 (k r : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

end GroupIsoDepth.LowerBounds


