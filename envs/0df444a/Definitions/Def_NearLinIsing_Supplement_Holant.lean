-- Prove2me | Definitions.Def_NearLinIsing_Supplement_Holant
-- name    : NearLinIsing_Supplement_Holant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:30.520033+00:00
-- url     : https://prove2.me/theorems/0aa3d152-d4f1-4b0d-b86c-b82dc0ca8724
-- title:
--   Holant models with flow conservation over $\mathbb Z_q$, their component polymers (26) and $m_v(S)$
-- statement:
--   Let $H$ be a finite undirected loopless multigraph; parallel edges keep distinct identities. Fix a reference direction $e=(\mathrm{tail},\mathrm{head})$ for every physical edge, and identify an antisymmetric configuration $\xi:\vec E(H)\to\mathbb Z_q$ with its labels $\xi_e$ in those directions. The label seen at $v$ on an edge $e\ni v$ is $\epsilon_{v,e}\xi_e$, with $\epsilon_{v,e}=1$ if $v$ is the tail and $-1$ if $v$ is the head. Each vertex carries a signature $f_v:\mathbb Z_q^{E_v}\to\mathbb R_{\ge0}$ with $f_v(0)>0$ and $f_v(x)=0$ whenever $\sum_{a\in E_v}x_a\ne0$; nothing else is assumed.
--
--   Write $\operatorname{supp}\xi$ for the physical edges with nonzero label and $V(F)$ for the endpoints of an edge set $F$. A **component polymer** $C=(F_C,\xi^C)$ is a labelling $\xi^C$ (zero outside $F_C$) whose support $F_C$ is nonempty and connected, with positive weight
--
--   $$w_C=\prod_{v\in V(F_C)}\frac{f_v(\xi^C_v)}{f_v(0)},\qquad A_{CD}=\mathbf 1\{V(F_C)\cap V(F_D)\neq\varnothing\}.\qquad(26)$$
--
--   Two polymers are compatible iff their vertex sets are disjoint, so $A$ includes the diagonal and the polymers form a polymer model in the sense of Definition 1.4, with $\lambda_{\max}(AW)$ as in §2.4.
--
--   For $S\subseteq\delta_H(v)$ (the edges at $v$), $m_v(S)=\max_{\operatorname{supp}\zeta=S}f_v(\zeta)/f_v(0)$. An edge set $F$ is a **nonempty connected bridgeless support** if $F\ne\varnothing$, $(V(F),F)$ is connected, and removing any one edge of $F$ leaves its endpoints joined by edges of $F$; $\delta_F(v)$ is the set of edges of $F$ at $v$.
--
--   These are the objects of the Holant criterion, Theorem 6.1.
--
--   **Formalization Note** The vertex and edge sets are arbitrary finite types; the copies $E_v$ with tail $v$ are indexed by the physical edges at $v$ (a bijection because $H$ is loopless). The polymer model is the published `NearLinIsing.PolymerModel`.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §6.1, pp. 32–33 (Holant model, component polymers (26), m_v(S))

import Mathlib
import Definitions.Def_NearLinIsing_Polymer

namespace NearLinIsing

namespace Supplement

noncomputable section

open Classical

/-!
# Holant models with flow conservation and their component polymers

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §6.1, pp. 32–33: the Holant model, its signatures, the component
polymers (26) and the local maxima `m_v(S)` used in Theorem 6.1.

`H` is a finite undirected loopless multigraph: a finite vertex type `V`, a finite edge type `E`
(parallel edges are distinct elements of `E`) and the endpoints `ends e = (tail, head)` of each
edge in a fixed reference direction. Each physical edge `e` has the two directed copies `a_e`
(from `tail` to `head`) and `ā_e`.

**Formalization Note.**
* Antisymmetric configurations `ξ : E⃗(H) → Z_q` are identified with their labels in the reference
  directions, `ξ : E → ZMod q`, as the paper does ("fix one reference direction per physical edge
  and identify ξ with its labels in those directions", p. 33). The label seen at `v` on an edge `e`
  at `v` is `ξ_e` if `v` is the tail of `e` and `−ξ_e` if `v` is the head (`ϵ_{v,e} ξ_e`). Because
  `H` is loopless, `E_v` (the copies with tail `v`) is in bijection with the physical edges at `v`,
  `δ_H(v)`; the type `Inc v` indexes both.
* A signature is `f_v : Z_q^{E_v} → ℝ` with `f_v ≥ 0`, `f_v(0) > 0` and `f_v(x) = 0` whenever
  `∑_{a ∈ E_v} x_a ≠ 0`; nothing else (no symmetry, no factorization) is assumed.
* A polymer `C = (F_C, ξ^C)` is determined by its labels `ξ^C` (zero outside `F_C`): it is a
  labelling whose support `F_C = supp ξ^C` is nonempty and connected and whose weight
  `w_C = ∏_{v ∈ V(F_C)} f_v(ξ^C_v)/f_v(0)` is positive. `V(F)` is the set of endpoints of `F`.
* Two polymers are compatible iff their vertex sets are disjoint, so `A_{CD} = 1{V(F_C) ∩ V(F_D) ≠
  ∅}` includes the diagonal; the polymers form a published `NearLinIsing.PolymerModel`, whose
  `LambdaMaxLe` is `λmax(AW)` in the Rayleigh sense of §2.4.
* `(V(F), F)` is connected when any two of its vertices are joined by a path of edges of `F`; it is
  bridgeless when removing any one edge of `F` leaves its endpoints joined in `F` (so two parallel
  edges are never bridges).
-/

/-- A **Holant model with flow conservation** on a finite loopless multigraph, with labels in
`Z_q` (§6.1, pp. 32–33). -/
structure Holant (q : ℕ) (V E : Type) [Fintype E] where
  /-- the endpoints `(tail, head)` of each physical edge in its reference direction -/
  ends : E → V × V
  loopless : ∀ e, (ends e).1 ≠ (ends e).2
  /-- the signature `f_v` on the labels of the edges at `v`, seen from `v` -/
  f : (v : V) → ({e : E // (ends e).1 = v ∨ (ends e).2 = v} → ZMod q) → ℝ
  f_nonneg : ∀ v x, 0 ≤ f v x
  f_zero_pos : ∀ v, 0 < f v 0
  f_conserve : ∀ v x, ∑ a, x a ≠ 0 → f v x = 0

namespace Holant

variable {q : ℕ} {V E : Type} [Fintype V] [Fintype E] (H : Holant q V E)

/-- `v` is an endpoint of `e`. -/
def IsEnd (v : V) (e : E) : Prop := (H.ends e).1 = v ∨ (H.ends e).2 = v

/-- `δ_H(v)`: the physical edges at `v` (equivalently the copies `E_v` with tail `v`). -/
abbrev Inc (v : V) : Type := {e : E // (H.ends e).1 = v ∨ (H.ends e).2 = v}

/-- The labels of `ξ` seen at `v`: `ξ_e` on an edge with tail `v`, `−ξ_e` on an edge with head
`v`. -/
def localView (ξ : E → ZMod q) (v : V) : H.Inc v → ZMod q :=
  fun e => if (H.ends e.1).1 = v then ξ e.1 else -ξ e.1

/-- `supp ξ`: the physical edges with nonzero label. -/
def supp (ξ : E → ZMod q) : Finset E := Finset.univ.filter fun e => ξ e ≠ 0

/-- `V(F)`: the endpoints of the edges of `F`. -/
def verts (F : Finset E) : Finset V := F.biUnion fun e => {(H.ends e).1, (H.ends e).2}

/-- `u` and `w` are joined by an edge of `F`. -/
def AdjIn (F : Finset E) (u w : V) : Prop :=
  ∃ e ∈ F, ((H.ends e).1 = u ∧ (H.ends e).2 = w) ∨ ((H.ends e).1 = w ∧ (H.ends e).2 = u)

/-- `(V(F), F)` is connected. -/
def IsConnected (F : Finset E) : Prop :=
  ∀ u ∈ H.verts F, ∀ w ∈ H.verts F, Relation.ReflTransGen (H.AdjIn F) u w

/-- `(V(F), F)` has no bridge: removing any one edge of `F` leaves its endpoints joined. -/
def IsBridgeless (F : Finset E) : Prop :=
  ∀ e ∈ F, Relation.ReflTransGen (H.AdjIn (F.erase e)) (H.ends e).1 (H.ends e).2

/-- A **nonempty connected bridgeless support** `F ⊆ E(H)` (Theorem 6.1, (28)). -/
def IsSupport (F : Finset E) : Prop := F.Nonempty ∧ H.IsConnected F ∧ H.IsBridgeless F

/-- The weight `w_C = ∏_{v ∈ V(F_C)} f_v(ξ^C_v)/f_v(0)` of a labelling, (26). -/
def polyWeight (ξ : E → ZMod q) : ℝ :=
  ∏ v ∈ H.verts (supp ξ), H.f v (H.localView ξ v) / H.f v 0

/-- `ξ` is (the labelling of) a component polymer: its support is nonempty and connected and its
weight is positive (§6.1, p. 33). -/
def IsPolymer (ξ : E → ZMod q) : Prop :=
  (supp ξ).Nonempty ∧ H.IsConnected (supp ξ) ∧ 0 < H.polyWeight ξ

/-- The component polymers `C = (F_C, ξ^C)`. -/
def Poly : Type := {ξ : E → ZMod q // H.IsPolymer ξ}

instance [NeZero q] : Fintype H.Poly := by
  unfold Poly; infer_instance

omit [Fintype V] in
/-- The vertex set `V(F_C)` of a polymer is nonempty. -/
lemma verts_nonempty (C : H.Poly) : (H.verts (supp C.1)).Nonempty := by
  obtain ⟨e, he⟩ := C.2.1
  exact ⟨(H.ends e).1, Finset.mem_biUnion.2 ⟨e, he, by simp⟩⟩

/-- The component polymers as a polymer model: activity `w_C`, compatibility = disjoint vertex sets
(so `A_{CD} = 1{V(F_C) ∩ V(F_D) ≠ ∅}`, diagonal included), (26). -/
def polymerModel : PolymerModel H.Poly where
  w C := H.polyWeight C.1
  compat C D := Disjoint (H.verts (supp C.1)) (H.verts (supp D.1))
  symm _ _ h := h.symm
  irrefl C h := by
    obtain ⟨v, hv⟩ := H.verts_nonempty C
    exact Finset.disjoint_left.1 h hv hv

/-- `δ_F(v)`: the edges of `F` at `v`. -/
def incIn (F : Finset E) (v : V) : Finset (H.Inc v) := Finset.univ.filter fun e => e.1 ∈ F

/-- The support of a local labelling `ζ ∈ Z_q^{E_v}`. -/
def localSupp {v : V} (ζ : H.Inc v → ZMod q) : Finset (H.Inc v) :=
  Finset.univ.filter fun e => ζ e ≠ 0

/-- `m_v(S) = max_{supp ζ = S} f_v(ζ)/f_v(0)` for `S ⊆ δ_H(v)` (§6.1, p. 33). -/
def mv (v : V) (S : Finset (H.Inc v)) : ℝ :=
  ⨆ ζ : {ζ : H.Inc v → ZMod q // H.localSupp ζ = S}, H.f v ζ.1 / H.f v 0

end Holant

end

end Supplement

end NearLinIsing


