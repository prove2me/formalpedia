-- Prove2me | Definitions.Def_DirectedHamiltonicity_Main_DetSum
-- name    : DirectedHamiltonicity_Main_DetSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:38.407454+00:00
-- url     : https://prove2.me/theorems/c0059d8a-ded9-44bd-ba4b-0a399aa8158c
-- title:
--   The determinant-sum objects: normalized weighted multigraphs, $H_X(R)$, $\mathcal X(R)$ and $\mathcal X_a(R)$
-- statement:
--   Let $H$ be a directed multigraph with arc weights $w:E(H)\to\mathbb Z_{\ge0}$, let $s\ne t$ be vertices, and let $I=V\setminus\{s,t\}$ be the internal vertices. Every arc carries the monomial $p(e)=y^{w(e)}\in\mathbb F_2[y]$.
--
--   1. $H$ is **normalized** when it has no loops, no arc entering $s$, no arc leaving $t$, and parallel arcs have distinct weights (the assumptions of §4.1).
--   2. $W_i$ is the set of weights of arcs entering $i$, and $d_i=|W_i|$.
--   3. For $X\subseteq I$, $H_X$ deletes every arc leaving a vertex of $I\setminus X$. For $R=(R_i)_{i\in I}$ with $R_i\subseteq W_i$, $H_X(R)$ adds to $H_X$ one arc $t\to i$ of weight $b$ (label $y^b$) for each $i\in I$ and $b\in R_i$.
--   4. $\mathcal X(R)$ is the family of $X\subseteq I$ for which $L_s(H_X(R),p)$ has no zero row indexed by a vertex of $I\setminus X$.
--   5. $s_i\in\mathbb F_2^{W_i}$ is the vector of coefficients of $y^b$, $b\in W_i$, in the diagonal entry $L_s(H_X(R),p)_{ii}$; it depends on $X$ and $R$.
--   6. For $a=(a_i)_{i\in I}$ with $a_i=(\alpha_i,\beta_i)\in\mathbb F_2^{1+d_i}$, $\mathcal X_a(R)$ is the family of $X\subseteq I$ whose indicators $x_i=\mathbf 1[i\in X]$ satisfy
--   $$\alpha_i x_i+\beta_i^{\top}s_i=1\qquad(i\in I)$$
--   over $\mathbb F_2$ (Equation (1)).
--
--   These objects underlie the determinant-sum algorithm of §4.
--
--   **Formalization Note** Subsets of $I$ are `Finset (Internal s t)`. $R_i$ is a subset of the finite type $W_i$; the added arcs are the pairs $(i,b)$, $b\in R_i$. A vector $a_i$ is a function `Option W_i → ZMod 2`, the coordinate `none` being $\alpha_i$.
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.8 / printed p.7 (§4, normalization, Laplacian, I, H_X), PDF pp.9–10 / printed pp.8–9 (W_i, R_i, H_X(R), 𝒳(R), s_i, d_i, Equation (1), 𝒳_a(R))

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs

namespace DirectedHamiltonicity.Main

open Multidigraph

/-!
# §4: the determinant-sum objects

T. Koana, S. Kumabe, STOC 2027 submission #811 (October 2026), §4.1–§4.2 (PDF pp.8–10 / printed
pp.7–9).

`H` is a directed multigraph with arc weights `w : E → ℕ`, and `s ≠ t` are vertices. The internal
vertices are `I = V ∖ {s, t}`. For `X ⊆ I`, `H_X` deletes every arc leaving a vertex of `I ∖ X`. For
`i ∈ I`, `W_i` is the set of weights of arcs entering `i`; `R_i ⊆ W_i`, and `H_X(R)` adds to `H_X` one
arc `t → i` of weight `b` for each `b ∈ R_i`. Every arc `e` carries the monomial `p(e) = y^{w(e)}` over
`𝔽₂[y]`.
-/

open Polynomial

variable {V E : Type}

/-- The internal vertices `I = V ∖ {s, t}`. -/
abbrev Internal (s t : V) := {v : V // v ≠ s ∧ v ≠ t}

namespace Multidigraph

/-- The standing assumptions of §4.1 after normalization (PDF p.8): no loops, no arc entering `s`,
no arc leaving `t`, and parallel arcs have distinct weights. -/
def IsNormalized (H : Multidigraph V E) (w : E → ℕ) (s t : V) : Prop :=
  H.Loopless ∧ (∀ e, H.head e ≠ s) ∧ (∀ e, H.tail e ≠ t) ∧
  ∀ e e', e ≠ e' → H.tail e = H.tail e' → H.head e = H.head e' → w e ≠ w e'

open Classical in
/-- `W_v`: the set of weights of the arcs entering `v`. -/
noncomputable def incomingWeights [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (v : V) :
    Finset ℕ :=
  (Finset.univ.filter (fun e => H.head e = v)).image w

/-- The arc `e` survives in `H_X`: its tail is not a vertex of `I ∖ X`. -/
def KeepArc (H : Multidigraph V E) (s t : V) (X : Finset (Internal s t)) (e : E) : Prop :=
  ∀ h : H.tail e ≠ s ∧ H.tail e ≠ t, (⟨H.tail e, h⟩ : Internal s t) ∈ X

/-- `H_X`: delete all arcs leaving vertices in `I ∖ X`. -/
def subX (H : Multidigraph V E) (s t : V) (X : Finset (Internal s t)) :
    Multidigraph V {e // H.KeepArc s t X e} :=
  H.restrictArcs (H.KeepArc s t X)

/-- The added arcs of `H_X(R)`: one arc `t → i` for each `i ∈ I` and each weight `b ∈ R_i`. -/
abbrev AugArc [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :=
  Σ i : Internal s t, (R i)

/-- The multigraph of the added arcs `t → i`, `b ∈ R_i`. -/
def augGraph [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    Multidigraph V (H.AugArc w s t R) :=
  ⟨fun _ => t, fun a => a.1.1⟩

/-- `H_X(R)`: `H_X` together with the added arcs `t → i` of weight `b ∈ R_i`. -/
def subXR [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V) (X : Finset (Internal s t))
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    Multidigraph V ({e // H.KeepArc s t X e} ⊕ H.AugArc w s t R) :=
  (H.subX s t X).addArcs (H.augGraph w s t R)

/-- The labels `p(e) = y^{w(e)} ∈ 𝔽₂[y]` on the arcs of `H_X(R)`; an added arc of weight `b` gets
`y^b`. -/
noncomputable def subXRLabel [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (X : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    ({e // H.KeepArc s t X e} ⊕ H.AugArc w s t R) → (ZMod 2)[X] :=
  Sum.elim (fun e => (Polynomial.X : (ZMod 2)[X]) ^ w e.1)
    (fun a => (Polynomial.X : (ZMod 2)[X]) ^ ((a.2 : _) : ℕ))

/-- The matrix `L_s(H_X(R), p)`. -/
noncomputable def augLaplacian [Fintype V] [Fintype E] [DecidableEq V] (H : Multidigraph V E) (w : E → ℕ)
    (s t : V) (X : Finset (Internal s t))
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    Matrix {v // v ≠ s} {v // v ≠ s} (ZMod 2)[X] := by
  classical
  exact (H.subXR w s t X R).reducedLaplacian (H.subXRLabel w s t X R) s

open Classical in
/-- `𝒳(R)`: the subsets `X ⊆ I` for which `L_s(H_X(R), p)` has no zero row indexed by `I ∖ X`. -/
noncomputable def survivors [Fintype V] [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) : Finset (Finset (Internal s t)) :=
  Finset.univ.filter fun X =>
    ∀ i : Internal s t, i ∉ X → (H.augLaplacian w s t X R) ⟨i.1, i.2.1⟩ ≠ 0

open Classical in
/-- `s_i ∈ 𝔽₂^{W_i}`: the vector of coefficients of `y^b`, `b ∈ W_i`, in the diagonal entry
`L_s(H_X(R), p)_{ii}`. -/
noncomputable def diagCoeffs [Fintype V] [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (X : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (i : Internal s t) : H.incomingWeights w i.1 → ZMod 2 :=
  fun b => ((H.augLaplacian w s t X R) ⟨i.1, i.2.1⟩ ⟨i.1, i.2.1⟩).coeff (b : ℕ)

/-- A coefficient vector `a_i = (α_i, β_i) ∈ 𝔽₂^{1 + d_i}`, `d_i = |W_i|`: the coordinate `none` is
`α_i`, the coordinate `some b` is `β_i(b)`. -/
abbrev CoeffVec [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (i : V) :=
  Option (H.incomingWeights w i) → ZMod 2

/-- Tuples `a = (a_i)_{i ∈ I}` of nonzero vectors `a_i ∈ 𝔽₂^{1 + d_i} ∖ {0}`. -/
abbrev NonzeroCoeffs [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V) :=
  (i : Internal s t) → {a : H.CoeffVec w i.1 // a ≠ 0}

open Classical in
/-- `𝒳_a(R)` (Equation (1), PDF p.10): the subsets `X ⊆ I` whose indicator `x_i = 1[i ∈ X]`
satisfies `α_i x_i + β_iᵀ s_i = 1` over `𝔽₂` for every `i ∈ I`. -/
noncomputable def sampled [Fintype V] [Fintype E] (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (a : (i : Internal s t) → H.CoeffVec w i.1)
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) : Finset (Finset (Internal s t)) :=
  Finset.univ.filter fun X =>
    ∀ i : Internal s t,
      a i none * (if i ∈ X then 1 else 0) +
        ∑ b, a i (some b) * H.diagCoeffs w s t X R i b = 1

end Multidigraph

end DirectedHamiltonicity.Main


