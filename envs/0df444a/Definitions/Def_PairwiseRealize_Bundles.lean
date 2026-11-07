-- Prove2me | Definitions.Def_PairwiseRealize_Bundles
-- name    : PairwiseRealize_Bundles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:39.425819+00:00
-- url     : https://prove2.me/theorems/79957464-4b98-45ef-ac3e-1a712234d3e1
-- title:
--   §A.1, p.10 — raw and accepted rectangular bundles, their four endpoints, and the cross-pair change vector $g$
-- statement:
--   Let $A,B\subseteq[n]$ be disjoint nonempty coordinate groups. A **raw rectangular bundle** is an ordered pair of distinct strings $(U_0,V_0)$ on $A$, an ordered pair of distinct strings $(W_0,Z_0)$ on $B$, and an assignment of the coordinates outside $A\cup B$, all uniform and independent. Its four endpoints are the rows $(U_0,W_0)$, $(V_0,Z_0)$, $(U_0,Z_0)$, $(V_0,W_0)$ with that outside assignment; the alternatives are the first two and the last two. The cross-pair moments change by
--
--   $$g_{ij}=(U_{0,i}-V_{0,i})(W_{0,j}-Z_{0,j}),\qquad (i,j)\in A\times B,$$
--
--   a vector of the Euclidean space $\mathbb R^{A\times B}$. A bundle is **accepted** for a forbidden set $D$ when all four endpoints avoid $D$. For a list $C$ of endpoints, $X_C=\sum_{x\in C}v_xv_x^{\mathsf T}$.
--
--   **Formalization Note** The raw law is the uniform law on the finite set `rawBundles`, so conditioning on acceptance is the uniform law on `acceptedBundles`, and $k$ independent accepted bundles with fair bits is the uniform law on $(\text{accepted}\times\{0,1\})^k$.
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

namespace PairwiseRealize

/-!
# Rectangular bundles and their deletion-conditioned law

K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean Statistics*, STOC 2027 submission
(manuscript sha256 62090516…), §A.1 "Conditioned correction bundles", printed p.10 (PDF p.11):
"A raw rectangular bundle uses disjoint nonempty coordinate groups A and B. It samples an
independent uniform ordered pair of distinct strings (U0, V0) on A and (W0, Z0) on B, together with
an independent uniform assignment outside A ∪ B. Its alternatives are {(U0, W0), (V0, Z0)},
{(U0, Z0), (V0, W0)}. Only the d = |A||B| cross-pair moments change, by
gij = (U0,i − V0,i)(W0,j − Z0,j)." "Let E_D mean that all endpoints avoid D."

**Formalization Note** A bundle's data is a tuple `(u, v, w, z, o)`: strings `u, v` on `A`, `w, z`
on `B`, and `o` on the coordinates outside `A ∪ B`. The raw law is the uniform law on the tuples
with `u ≠ v` and `w ≠ z` (`rawBundles`); conditioning it on `E_D` gives the uniform law on the
accepted tuples (`acceptedBundles`). "k independent accepted bundles and independent fair baseline
bits" is the uniform law on `(acceptedBundles × Bool)^k`, so its probabilities are counting
ratios. The four endpoints are `(u,w,o)`, `(v,z,o)`, `(u,z,o)`, `(v,w,o)`, indexed `0, 1, 2, 3`.
-/

/-- The data of a rectangular bundle on the coordinate groups `A, B`: strings `u, v` on `A`,
`w, z` on `B`, and an assignment `o` of the coordinates outside `A ∪ B`. -/
@[ext]
structure BundleData (n : ℕ) (A B : Finset (Fin n)) where
  u : A → Bool
  v : A → Bool
  w : B → Bool
  z : B → Bool
  o : {i : Fin n // i ∉ A ∪ B} → Bool
  deriving DecidableEq

/-- `BundleData` is the product of its five fields. -/
def BundleData.equivProd (n : ℕ) (A B : Finset (Fin n)) :
    BundleData n A B ≃
      (A → Bool) × (A → Bool) × (B → Bool) × (B → Bool) × ({i : Fin n // i ∉ A ∪ B} → Bool) where
  toFun c := (c.u, c.v, c.w, c.z, c.o)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) (A B : Finset (Fin n)) : Fintype (BundleData n A B) :=
  Fintype.ofEquiv _ (BundleData.equivProd n A B).symm

/-- The row that takes `a` on `A`, `b` on `B` and `o` elsewhere (on `A ∩ B`, which is empty for a
bundle, it takes `a`). -/
def glue {n : ℕ} {A B : Finset (Fin n)} (a : A → Bool) (b : B → Bool)
    (o : {i : Fin n // i ∉ A ∪ B} → Bool) : Row n := fun i =>
  if hA : i ∈ A then a ⟨i, hA⟩ else
    if hB : i ∈ B then b ⟨i, hB⟩ else o ⟨i, by simp [hA, hB]⟩

/-- The four endpoints of a bundle: `0 ↦ (U0,W0)`, `1 ↦ (V0,Z0)` (the first alternative) and
`2 ↦ (U0,Z0)`, `3 ↦ (V0,W0)` (the second alternative), each with the outside assignment. -/
def endpoint {n : ℕ} {A B : Finset (Fin n)} (c : BundleData n A B) : Fin 4 → Row n
  | 0 => glue c.u c.w c.o
  | 1 => glue c.v c.z c.o
  | 2 => glue c.u c.z c.o
  | 3 => glue c.v c.w c.o

/-- The support of the raw law: the bundles with `u ≠ v` and `w ≠ z` ("ordered pairs of distinct
strings"). -/
def rawBundles (n : ℕ) (A B : Finset (Fin n)) : Finset (BundleData n A B) :=
  Finset.univ.filter fun c => c.u ≠ c.v ∧ c.w ≠ c.z

/-- The accepted bundles: the raw bundles all of whose endpoints avoid `D` (the event `E_D`). -/
def acceptedBundles (n : ℕ) (A B : Finset (Fin n)) (D : Finset (Row n)) :
    Finset (BundleData n A B) :=
  (rawBundles n A B).filter fun c => ∀ k, endpoint c k ∉ D

/-- The cross-pair change vector `g ∈ ℝ^{A×B}`, `g_{ij} = (U0,i − V0,i)(W0,j − Z0,j)`, as a vector of
the Euclidean space on `A × B` (whose unit ball is `B_d`, `d = |A||B|`). -/
def gvec {n : ℕ} {A B : Finset (Fin n)} (c : BundleData n A B) : EuclideanSpace ℝ (A × B) :=
  WithLp.toLp 2 fun ij =>
    ((bv (c.u ij.1) - bv (c.v ij.1)) * (bv (c.w ij.2) - bv (c.z ij.2)) : ℤ)

/-- The baseline bit `q⁰ ∈ {0,1}` as a real number. -/
def bitR (b : Bool) : ℝ := (bv b : ℝ)

/-- `X_C = Σ_{x∈C} v_x v_xᵀ` for the endpoint list of a bundle-like object, (A.3). -/
def Xmat (n : ℕ) {a : ℕ} (e : Fin a → Row n) : Matrix (Feat n) (Feat n) ℝ :=
  ∑ k, Matrix.vecMulVec (vR n (e k)) (vR n (e k))

end PairwiseRealize


