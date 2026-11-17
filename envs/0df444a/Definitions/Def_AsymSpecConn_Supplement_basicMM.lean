-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_basicMM
-- name    : AsymSpecConn_Supplement_basicMM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:20:37.747291+00:00
-- url     : https://prove2.me/theorems/ed7a78a4-7b9c-452e-a500-3063d785345e
-- title:
--   Basic matrix-multiplication and polynomial-multiplication tensor families
-- statement:
--   Over a field $K$, define the three **basic matrix-multiplication tensors**
--
--   $$
--   b_1=\langle2,1,1\rangle,\qquad b_2=\langle1,2,1\rangle,\qquad b_3=\langle1,1,2\rangle,
--   $$
--
--   and their flattening polytope $\Gamma=\operatorname{conv}\{(1,1,0),(0,1,1),(1,0,1)\}$. For positive integers $m,n$, the **polynomial-multiplication tensor** is
--
--   $$
--   P_{m,n}=\sum_{u=1}^{m}\sum_{v=1}^{n}e_u\otimes e_v\otimes e_{u+v-1},
--   $$
--
--   together with all permutations of its three legs. The module also defines the paper's $i$-irreducibility condition over an arbitrary field: a concise representative is fixed by a finite-group action whose representation on leg $i$ is irreducible.
--
--   These objects support the star-convexity results in §§3.6 and 4.
--
--   **Formalization Note** Legs and bases are zero-indexed. The polynomial tensor is embedded in a common ambient space $K^{m+n-1}$ on all three legs; projection back to $K^m\otimes K^n\otimes K^{m+n-1}$ and inclusion in the other direction make the two representatives mutually restrictive.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), eq. (8) and Theorems 3.11–3.12 pp.27–28; Definition 4.4 p.32

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_permutation
import Definitions.Def_AsymSpecConn_flatRank

set_option autoImplicit false

open PiTensorProduct BigOperators

namespace AsymSpecConn.Supplement

universe u

/-- The three basic rectangular matrix-multiplication tensors
`b₁ = ⟨2,1,1⟩`, `b₂ = ⟨1,2,1⟩`, `b₃ = ⟨1,1,2⟩` (p.27 over `ℂ`, and p.34 over an
arbitrary field), as tensor-equivalence classes. Legs use `Fin 3`, so source leg 1 has index 0. -/
noncomputable def basicMM (K : Type u) [Field K] : Fin 3 → MME.TensorQ K 3 :=
  ![MME.TensorQ.toQ (MME.MMObj K 2 1 1),
    MME.TensorQ.toQ (MME.MMObj K 1 2 1),
    MME.TensorQ.toQ (MME.MMObj K 1 1 2)]

/-- `Γ = conv{(1,1,0),(0,1,1),(1,0,1)}` (p.27), the full flattening-rank polytope
for the three basic matrix-multiplication tensors. -/
noncomputable def gamma3 : Set (Fin 3 → ℝ) :=
  convexHull ℝ ({![1, 1, 0], ![0, 1, 1], ![1, 0, 1]} : Set (Fin 3 → ℝ))

/-- The polynomial-multiplication tensor
`P_{m,n} = ∑_{u=1}^m ∑_{v=1}^n e_u ⊗ e_v ⊗ e_{u+v-1}` (eq. (8), p.27).

**Formalization Note** Basis indices are zero-based, so the third basis vector is indexed by
`u+v` rather than `u+v-1`. All three legs are placed in the common coordinate space
`K^{m+n-1}`; the first two use only their first `m` and `n` basis vectors. Inclusion followed by
projection identifies this object, up to mutual restriction, with the source object in
`K^m ⊗ K^n ⊗ K^{m+n-1}`. -/
noncomputable def polyMulObj (K : Type u) [Field K] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    MME.TensorObj K 3 where
  V _ := Fin (m + n - 1) → K
  fin _ := Module.Finite.pi
  t := ∑ a : Fin m, ∑ b : Fin n, tprod K (fun
    | ⟨0, _⟩ => (Pi.single ⟨a.val, by omega⟩ 1 : Fin (m + n - 1) → K)
    | ⟨1, _⟩ => (Pi.single ⟨b.val, by omega⟩ 1 : Fin (m + n - 1) → K)
    | ⟨2, _⟩ => (Pi.single ⟨a.val + b.val, by omega⟩ 1 : Fin (m + n - 1) → K)
    | ⟨i + 3, hi⟩ => absurd hi (by omega))

/-- A leg-permuted polynomial-multiplication tensor `π P_{m,n}` (pp.27--28).
`permObj π` moves source leg `i` to position `π(i)` under the convention documented in the
published permutation module. -/
noncomputable def permutedPolyMul (K : Type u) [Field K] (pi : Equiv.Perm (Fin 3))
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : MME.TensorQ K 3 :=
  MME.TensorQ.toQ (MME.TensorObj.permObj pi (polyMulObj K m n hm hn))

/-- The arbitrary-field version of the paper's `i`-irreducibility predicate (p.30): an
equivalence class has a concise representative fixed by a finite-group action whose action on
leg `i` is irreducible. -/
def FieldIrreducible {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (i : Fin k)
    (s : MME.TensorQ K k) : Prop :=
  ∃ X : MME.TensorObj K k, MME.TensorQ.toQ X = s ∧ AsymSpecConn.IsConcise hk X ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (rho : ∀ j, Representation K G (X.V j)),
      (rho i).IsIrreducible ∧ ∀ g : G, PiTensorProduct.map (fun j => rho j g) X.t = X.t

end AsymSpecConn.Supplement


