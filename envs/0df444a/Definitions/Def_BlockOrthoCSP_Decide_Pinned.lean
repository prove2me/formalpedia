-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Pinned
-- name    : BlockOrthoCSP_Decide_Pinned
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:11:46.86437+00:00
-- url     : https://prove2.me/theorems/94b7809c-ea9f-4da8-995c-3e97baaa4c77
-- title:
--   Similar constraint-function families, labelled instances, pinned partition values $Z^H_\beta(I)$, isomorphisms and twins
-- statement:
--   Two **similar** finite families $\mathcal H$, $\mathcal G$ of constraint functions over finite domains $D_{\mathcal H}$, $D_{\mathcal G}$ and a common coefficient ring are given as two families indexed by the same finite index set with the same arities (the arity-preserving bijection $h \leftrightarrow g$ is the common index). A **$k$-labelled instance** has variables $1,\dots,k$ (labelled) and $h \ge 0$ unlabelled ones, and a list of constraints (index, ordered scope); retargeting it from $\mathcal H$ to $\mathcal G$ keeps the same data. Its **pinned partition value** with pin $\beta : [k] \to D_{\mathcal H}$ is
--   $$Z^{\mathcal H}_\beta(I) = \sum_{y \in D_{\mathcal H}^{h}} \prod_{(h; v_1,\dots,v_r)} h\big((\beta, y)_{v_1},\dots,(\beta,y)_{v_r}\big).$$
--   A bijection $\sigma : D_{\mathcal H} \to D_{\mathcal G}$ is an **isomorphism** if $h(a_1,\dots,a_r) = g(\sigma a_1,\dots,\sigma a_r)$ for every corresponding pair; $u, v$ are **twins** in $\mathcal G$ if replacing $u$ by $v$ in any one position of any $g$ leaves its value unchanged.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), pp. F-19–F-20, §F.5.2

import Mathlib

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-! Similar families, labelled instances over a family, pinned partition values, isomorphisms
and twins (§F.5.2, pp. F-19–F-20, after Young [You25]). Two similar families are given as two
families `H, G` indexed by the same finite index type `ι` with the same arities `ar`: the
arity-preserving bijection `h ↔ g` is the common index. -/

/-- A `k`-labelled instance over a family indexed by `ι` with arities `ar`: variables
`Fin (k + h)`, the first `k` carrying the labels `1, …, k`, the other `h` unlabelled (isolated
ones allowed); a list of constraints `(i; scope)` with multiplicity. Retargeting from `H` to a
similar `G` (`I_{H→G}`) keeps the same data. -/
structure FamInst {ι : Type} (ar : ι → ℕ) (k : ℕ) where
  h : ℕ
  cons : List (Σ i : ι, Fin (ar i) → Fin (k + h))

/-- The pinned partition value `Z^H_β(I)`: the sum over assignments of the unlabelled variables
of the product of constraint values, label `l` pinned to `β l`. -/
def pinnedValue {ι : Type} {ar : ι → ℕ} {D L : Type} [Fintype D] [CommRing L]
    (H : (i : ι) → (Fin (ar i) → D) → L) {k : ℕ} (I : FamInst ar k) (β : Fin k → D) : L :=
  ∑ y : Fin I.h → D, (I.cons.map fun c => H c.1 (Fin.append β y ∘ c.2)).prod

/-- `σ : D_H → D_G` is an isomorphism of the similar families:
`h(a_1, …, a_r) = g(σ a_1, …, σ a_r)` for every corresponding pair. -/
def IsFamilyIso {ι : Type} {ar : ι → ℕ} {DH DG L : Type}
    (H : (i : ι) → (Fin (ar i) → DH) → L) (G : (i : ι) → (Fin (ar i) → DG) → L)
    (σ : DH ≃ DG) : Prop :=
  ∀ (i : ι) (a : Fin (ar i) → DH), H i a = G i (σ ∘ a)

/-- `u, v` are twins in `G`: replacing `u` by `v` in any one position of any function of `G`
leaves its value unchanged. -/
def AreTwins {ι : Type} {ar : ι → ℕ} {D L : Type}
    (G : (i : ι) → (Fin (ar i) → D) → L) (u v : D) : Prop :=
  ∀ (i : ι) (p : Fin (ar i)) (a : Fin (ar i) → D),
    G i (Function.update a p u) = G i (Function.update a p v)

end BlockOrthoCSP.Decide


