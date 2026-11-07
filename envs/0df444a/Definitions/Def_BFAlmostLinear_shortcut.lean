-- Prove2me | Definitions.Def_BFAlmostLinear_shortcut
-- name    : BFAlmostLinear_shortcut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:59.208194+00:00
-- url     : https://prove2.me/theorems/f47ab623-d629-4079-85c2-3f44b1bd32db
-- title:
--   Shortcut arcs (S1)–(S5) with the clamped $\Delta'_r$
-- statement:
--   Let $G$ be a weighted graph with frozen flags (in the paper, the reweighted $G_\phi$) and $\Delta:V\to\mathbb R$. For a negative vertex $r$ with real flagged arc $(r,r')$ put
--   $$\Delta'_r=\min\{-\omega(r,r'),\ \max\{0,\Delta_r\}\},\qquad V^{\mathrm{out}}_r=\{v:d^1(r,v)<-\Delta'_r\},\qquad V^{\mathrm{in}}_r=\{v:d^0(v,r)<\Delta'_r\}.$$
--   The shortcut graph adds to $G$:
--
--   1. **(S1)** a Steiner vertex $\tilde r$ for each negative vertex $r$;
--   2. **(S2)** for $v\in V^{\mathrm{out}}_r\cup\{r'\}$ and a real arc $(v,w)$, the arc $(\tilde r,w)$ of weight $d^1(r,v)+\Delta'_r+\omega(v,w)$, if this is non-negative;
--   3. **(S3)** for $v\in V^{\mathrm{in}}_r\cup\{r\}$ and a real arc $(u,v)$, the arc $(u,\tilde r)$ of weight $\omega(u,v)+d^0(v,r)-\Delta'_r$, if this is non-negative;
--   4. **(S4)** for $v\in V^{\mathrm{out}}_r$ the tail of a real flagged arc $(v,v')$, the arc $(r,v')$ of weight $d^1(r,v)+\omega(v,v')$;
--   5. **(S5)** for $u'\in V^{\mathrm{in}}_r$ the head of a real flagged arc $(u,u')$, the arc $(u,r')$ of weight $\omega(u,u')+d^0(u',r)+\omega(r,r')$.
--
--   All new arcs are real; (S4) and (S5) arcs are flagged, (S2) and (S3) arcs are not.
--
--   **Formalization Note** $\Delta$ is arbitrary. A reweighting can make a frozen arc positive, and then $\Delta'_r=-\omega(r,r')<0$, as the printed clamp gives. The auxiliary arcs (S6), the final application of Lemma 1.2 and the data structure are not part of this graph. A negative vertex is represented by its real flagged arc, which (I1) makes unique.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), §4.3, Step 2 and Step 3, p.23

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-!
# The shortcut edges (S1)–(S5)

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Step 3 of §4.3, p.23.

**Formalization Note.**
* The input is the graph `G` being shortcut, which in the paper is the reweighted `G_ϕ` of Step 1, with its
  frozen flags; `Δ` is an arbitrary real function. A reweighting can make a frozen arc positive (§1.1, p.2),
  and then the printed clamp has `∆′_r = −ω(r, r′) < 0`.
* A negative vertex `r` is represented by its real flagged arc `(r, r′)`, a `NegArc`: under (I1) the arc is
  determined by `r`. The Steiner vertex `r̃` is `Sum.inr` of that arc.
* The distances `d⁰`, `d¹` are of the real arcs, and `(S2)–(S5)` start from real arcs, because those arcs are
  real and shortcut real walks (p.24, Claim 4.10). The arcs `(S2)–(S3)` are unflagged; the arcs `(S4)–(S5)`
  are flagged whatever their weight (p.25, "the single (negative) edge"). The auxiliary arcs (S6), the final
  application of Lemma 1.2 (p.24) and the data structure are not part of this graph.
* A weight `d¹(r, v) + …` uses `EReal.toReal`. On the arcs below, `d¹(r, v) < −∆′_r` or `v = r′`, and
  `d⁰(v, r) < ∆′_r` or `v = r`, so under `Frozen` and (I1) the distance is finite and nothing is lost.
-/

variable {V E : Type}

namespace WGraph

variable (G : WGraph V E) (Δ : V → ℝ)

/-- `∆′_r = min{−ω(r, r′), max{0, ∆_r}}`, p.23. -/
noncomputable def clamp (r : G.NegArc) : ℝ := min (-G.w r.1) (max 0 (Δ (G.net.tail r.1)))

/-- `v ∈ V^out_r = {v ∈ V : d¹(r, v) < −∆′_r}`, p.23. -/
def InVout (r : G.NegArc) (v : V) : Prop := G.dH 1 (G.net.tail r.1) v < ((-(G.clamp Δ r) : ℝ) : EReal)

/-- `v ∈ V^in_r = {v ∈ V : d⁰(v, r) < ∆′_r}`, p.23. -/
def InVin (r : G.NegArc) (v : V) : Prop := G.dH 0 v (G.net.tail r.1) < ((G.clamp Δ r : ℝ) : EReal)

/-- The weight in (S2): `d¹(r, v) + ∆′_r + ω(v, w)` for the arc `e = (v, w)`. -/
noncomputable def s2Weight (r : G.NegArc) (e : E) : ℝ :=
  (G.dH 1 (G.net.tail r.1) (G.net.tail e)).toReal + G.clamp Δ r + G.w e

/-- The weight in (S3): `ω(u, v) + d⁰(v, r) − ∆′_r` for the arc `e = (u, v)`. -/
noncomputable def s3Weight (r : G.NegArc) (e : E) : ℝ :=
  G.w e + (G.dH 0 (G.net.head e) (G.net.tail r.1)).toReal - G.clamp Δ r

/-- The weight in (S4): `d¹(r, v) + ω(v, v′)` for the negative arc `e = (v, v′)`. -/
noncomputable def s4Weight (r e : G.NegArc) : ℝ :=
  (G.dH 1 (G.net.tail r.1) (G.net.tail e.1)).toReal + G.w e.1

/-- The weight in (S5): `ω(u, u′) + d⁰(u′, r) + ω(r, r′)` for the negative arc `e = (u, u′)`. -/
noncomputable def s5Weight (r e : G.NegArc) : ℝ :=
  G.w e.1 + (G.dH 0 (G.net.head e.1) (G.net.tail r.1)).toReal + G.w r.1

/-- The arcs of the shortcut graph, p.23:

* `old e`: an arc of `G`;
* `s2 r e`: (S2), for `v ∈ V^out_r ∪ {r′}` and a real arc `e = (v, w)` whose weight is non-negative, the arc
  `(r̃, w)`;
* `s3 r e`: (S3), for `v ∈ V^in_r ∪ {r}` and a real arc `e = (u, v)` whose weight is non-negative, the arc
  `(u, r̃)`;
* `s4 r e`: (S4), for `v ∈ V^out_r` the tail of a negative arc `e = (v, v′)`, the arc `(r, v′)`;
* `s5 r e`: (S5), for `u′ ∈ V^in_r` the head of a negative arc `e = (u, u′)`, the arc `(u, r′)`. -/
inductive ShortcutArc : Type
  | old (e : E)
  | s2 (r : G.NegArc) (e : E) (he : G.aux e = false)
      (hv : G.InVout Δ r (G.net.tail e) ∨ G.net.tail e = G.net.head r.1)
      (hw : 0 ≤ G.s2Weight Δ r e)
  | s3 (r : G.NegArc) (e : E) (he : G.aux e = false)
      (hv : G.InVin Δ r (G.net.head e) ∨ G.net.head e = G.net.tail r.1)
      (hw : 0 ≤ G.s3Weight Δ r e)
  | s4 (r e : G.NegArc) (hv : G.InVout Δ r (G.net.tail e.1))
  | s5 (r e : G.NegArc) (hv : G.InVin Δ r (G.net.head e.1))

/-- The graph `G` with the shortcut arcs (S1)–(S5), on the vertices `V ⊔ {r̃ : r ∈ N}`. -/
noncomputable def shortcut : WGraph (V ⊕ G.NegArc) (ShortcutArc G Δ) where
  net :=
    { tail := fun a => match a with
        | .old e => Sum.inl (G.net.tail e)
        | .s2 r _ _ _ _ => Sum.inr r
        | .s3 _ e _ _ _ => Sum.inl (G.net.tail e)
        | .s4 r _ _ => Sum.inl (G.net.tail r.1)
        | .s5 _ e _ => Sum.inl (G.net.tail e.1)
      head := fun a => match a with
        | .old e => Sum.inl (G.net.head e)
        | .s2 _ e _ _ _ => Sum.inl (G.net.head e)
        | .s3 r _ _ _ _ => Sum.inr r
        | .s4 _ e _ => Sum.inl (G.net.head e.1)
        | .s5 r _ _ => Sum.inl (G.net.head r.1) }
  w := fun a => match a with
    | .old e => G.w e
    | .s2 r e _ _ _ => G.s2Weight Δ r e
    | .s3 r e _ _ _ => G.s3Weight Δ r e
    | .s4 r e _ => G.s4Weight r e
    | .s5 r e _ => G.s5Weight r e
  neg := fun a => match a with
    | .old e => G.neg e
    | .s4 _ _ _ => true
    | .s5 _ _ _ => true
    | _ => false
  aux := fun a => match a with
    | .old e => G.aux e
    | _ => false

end WGraph

end BFAlmostLinear


