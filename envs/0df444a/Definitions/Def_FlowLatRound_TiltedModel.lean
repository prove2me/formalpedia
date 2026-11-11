-- Prove2me | Definitions.Def_FlowLatRound_TiltedModel
-- name    : FlowLatRound_TiltedModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:44.048033+00:00
-- url     : https://prove2.me/theorems/62372484-935b-442a-9691-42b7880dd58b
-- title:
--   §3.4 and App. C.4 — degree sequences, pairings, $G(\pi)$, the tilted configuration model (P1)–(P3), the law of $X$, $\mathbb E X^{-1/2}$, the birthday law, $\mathbb E\,S/V$ and $\mathbb E\,\Phi$
-- statement:
--   A **degree sequence** is $g=(g_1,\dots,g_n)$ with $g_i\ge1$ and $\sum_ig_i=2m$ even; its cycle rank is $d=m-n+1$, and $a_i=g_i-1$, $\alpha=\sum_ia_i$, $S_2=\sum_ia_i(a_i-1)$. Vertex $i$ carries $g_i$ labeled half-edges and $a_i$ labeled slots.
--
--   1. A **pairing** $\pi$ is a perfect matching of the half-edges; $G(\pi)$ is the multigraph whose edges are the pairs of $\pi$ (enumerated by their smaller half-edge, oriented from it).
--   2. The **tilted configuration model**: (P1) a labeled tree $t$ with probability $w(t)/\sum_{t'}w(t')$, $w(t)=\prod_i(g_i)_{\deg_t(i)}$; (P2) for each vertex an injection of the tree edges at $i$ into its half-edges, uniformly; (P3) a uniform perfect matching of the remaining half-edges. Its output is $(\pi,T)$, $T$ the edges of $G(\pi)$ that carry tree edges. $P[(\pi,T)]$ is the sum of the step probabilities over all outcomes producing $(\pi,T)$, and $P[\pi]=\sum_TP[(\pi,T)]$.
--   3. $X$ is the fundamental-cycle length of a uniformly random non-tree edge; $P(X=\ell)$ and $\mathbb E X^{-1/2}$ are taken under the model.
--   4. The **birthday process** draws slots uniformly without replacement; $X'$ is the number of draws made before some vertex (group) is drawn for the second time.
--   5. $\mathbb E_G\,S(K_G)/V(K_G)$ and $\mathbb E\,\Phi(K_G)$ are expectations over $P[\pi]$; the $q$-regular sequence is $g_i\equiv q$, and Theorem 1.1 uses $q=4$ on $n=d-1$ vertices.
--
--   **Formalization Note** The model is defined by its steps, not by the conclusion $P[\pi]\propto\tau(G(\pi))$ of Lemma 3.6.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), §3.4, p.8 (PDF 10); Proposition 3.7, p.9 (PDF 11); Appendix C.4–C.5, p.26 (PDF 28); Appendix C.7, p.28 (PDF 30)

import Mathlib
import Definitions.Def_FlowLatRound_FlowGraph
import Definitions.Def_FlowLatRound_LabeledTree

namespace FlowLatRound


/-! # The tilted configuration model, the cycle-length law and the birthday process

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), §3.4, p.8 (PDF 10: pairings, `G(π)`, `w_q`, steps
(P1)–(P3)); Appendix C.4, p.26 (PDF 28: degree sequences `(gᵢ)`, `aᵢ = gᵢ − 1`, `α`, slots);
Proposition 3.7, p.9 and Proposition C.7, p.26 (`X` and `X′`); Appendix C.7, p.28 (`S₂`).

**Formalization Note.**
* A degree sequence is `g : Fin n → ℕ` with `gᵢ > 0` and `Σ gᵢ` even; `m = Σ gᵢ / 2` and the cycle
  rank is `cr = m + 1 − n` (statements assume `cr ≥ 1` or `≥ 2`, so the subtraction is exact).
* Half-edges are `Σ i, Fin (gᵢ)`, ordered by `finSigmaFinEquiv` (vertex first, then label). A
  pairing is a fixed-point-free involution of the half-edges. The edges of `G(π)` are its pairs
  `{h, π h}`, enumerated in increasing order of the smaller half-edge `h`, and oriented from the
  vertex of `h` to the vertex of `π h`.
* The model is the **process** (P1)–(P3), not its conclusion: (P1) a labeled tree `t` with
  probability `w(t)/Σ w`, `w(t) = Π (gᵢ)_{deg_t(i)}`; (P2) for each vertex `i` an injection of the
  tree edges at `i` into the `gᵢ` half-edges of `i`, uniform; (P3) a uniform perfect matching of
  the remaining (residual) half-edges. The output is the pairing `π` (tree edges paired through
  their half-edges, residual half-edges by the matching) and the set `T` of edges of `G(π)`
  carrying tree edges. `processProb g π T` sums the step probabilities over all step outcomes
  producing `(π, T)`; `pairLaw g π` is the marginal law of `π`.
* `X` is the fundamental-cycle length of a uniformly random non-tree edge (`1/cr` each). The
  birthday process draws slots (vertex `i` has `aᵢ = gᵢ − 1` slots) uniformly without
  replacement; its first `ℓ + 1` draws form a uniform injective sequence. -/

/-- A degree sequence on `n` vertices: positive degrees with even sum (Appendix C.4, p.26). -/
structure DegSeq (n : ℕ) where
  g : Fin n → ℕ
  pos : ∀ i, 0 < g i
  even : Even (∑ i, g i)

namespace DegSeq

variable {n : ℕ} (g : DegSeq n)

/-- The number of edges `m = Σ gᵢ / 2`. -/
def m : ℕ := (∑ i, g.g i) / 2

/-- The cycle rank `d = m − n + 1`. -/
def cr : ℕ := g.m + 1 - n

/-- The number of slots `aᵢ = gᵢ − 1` of vertex `i` (Appendix C.4). -/
def a (i : Fin n) : ℕ := g.g i - 1

/-- `α = Σ aᵢ` (Appendix C.4). -/
def alpha : ℕ := ∑ i, g.a i

/-- `S₂ = Σ aᵢ (aᵢ − 1)` (Appendix C.7, p.28). -/
def S2 : ℝ := ∑ i, (g.a i : ℝ) * ((g.a i : ℝ) - 1)

/-- Half-edges: vertex `i` carries `gᵢ` labeled half-edges. -/
abbrev HalfEdge := Σ i : Fin n, Fin (g.g i)

/-- Slots: vertex `i` carries `aᵢ` labeled slots. -/
abbrev Slot := Σ i : Fin n, Fin (g.a i)

/-- The position of a half-edge in the order vertex-first, then label. -/
def heIdx (h : g.HalfEdge) : ℕ := (finSigmaFinEquiv h).1

/-- The smaller half-edges `h` (`h < f h`) of a map `f` on half-edges, in increasing order. -/
def lowHalves (f : g.HalfEdge → g.HalfEdge) : List g.HalfEdge :=
  (List.finRange (∑ i, g.g i)).filterMap (fun x =>
    let h := finSigmaFinEquiv.symm x
    if g.heIdx h < g.heIdx (f h) then some h else none)

theorem pos_n_of_edge (k : Fin g.m) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact absurd k.2 (by simp [DegSeq.m])
  · exact h

/-- A default half-edge (used only off the valid range). -/
def defaultHE (k : Fin g.m) : g.HalfEdge := ⟨⟨0, g.pos_n_of_edge k⟩, ⟨0, g.pos _⟩⟩

/-- The `k`-th pair `(h, f h)` of `f`, `h` the `k`-th smaller half-edge. -/
def pairOf (f : g.HalfEdge → g.HalfEdge) (k : Fin g.m) : g.HalfEdge × g.HalfEdge :=
  let h := (g.lowHalves f).getD k (g.defaultHE k)
  (h, f h)

/-- The oriented multigraph of the pairs of `f`: edge `k` runs from the vertex of the `k`-th
smaller half-edge to the vertex of its partner. -/
def graphOfFun (f : g.HalfEdge → g.HalfEdge) : MGraph n g.m :=
  ⟨fun k => (g.pairOf f k).1.1, fun k => (g.pairOf f k).2.1⟩

end DegSeq

/-- Perfect matchings of a finite set: fixed-point-free involutions. -/
def PerfMatch (X : Type) [Fintype X] [DecidableEq X] : Type :=
  {f : Equiv.Perm X // ∀ x, f (f x) = x ∧ f x ≠ x}

instance (X : Type) [Fintype X] [DecidableEq X] : Fintype (PerfMatch X) := by
  unfold PerfMatch; infer_instance

namespace DegSeq

variable {n : ℕ} (g : DegSeq n)

/-- Pairings: perfect matchings of the half-edges (§3.4, p.8). -/
abbrev Pairing := PerfMatch g.HalfEdge

/-- The multigraph `G(π)` of a pairing; its edges are labeled by the pairs of `π`. -/
def graphOf (π : g.Pairing) : MGraph n g.m := g.graphOfFun π.1

/-- The tilted weight `w(t) = Π_i (gᵢ)_{deg_t(i)}` of a labeled tree (§3.4, App. C.4). -/
def treeWeight (t : LTree n) : ℕ := ∏ i, (g.g i).descFactorial (degE t.1 i)

/-- Step (P1): the probability `w(t) / Σ_{t'} w(t')` of the labeled tree `t`. -/
noncomputable def p1 (t : LTree n) : ℝ := (g.treeWeight t : ℝ) / ∑ t', (g.treeWeight t' : ℝ)

/-- The tree edges at `i`. -/
abbrev TreeEdgesAt (t : LTree n) (i : Fin n) := {e : Sym2 (Fin n) // e ∈ t.1 ∧ i ∈ e}

/-- Outcomes of step (P2): for each vertex `i`, an injection of the tree edges at `i` into the
`gᵢ` half-edges of `i`. -/
abbrev Attach (t : LTree n) := (i : Fin n) → (TreeEdgesAt t i ↪ Fin (g.g i))

/-- A half-edge is residual if no tree edge is attached to it. -/
def IsResid (t : LTree n) (a : g.Attach t) (h : g.HalfEdge) : Prop :=
  ∀ x : TreeEdgesAt t h.1, a h.1 x ≠ h.2

instance (t : LTree n) (a : g.Attach t) : DecidablePred (g.IsResid t a) := by
  intro h; unfold IsResid; infer_instance

/-- The residual half-edges, matched in step (P3). -/
abbrev Resid (t : LTree n) (a : g.Attach t) := {h : g.HalfEdge // g.IsResid t a h}

/-- The outcome `(t, a, μ)` of (P1)–(P3) produces the pairing `π` with planted tree `T`: the two
half-edges of every tree edge are paired, residual half-edges are paired by `μ`, and `T` is the
set of edges of `G(π)` whose (smaller) half-edge carries a tree edge. -/
def Produces (t : LTree n) (a : g.Attach t) (μ : PerfMatch (g.Resid t a)) (π : g.Pairing)
    (T : Finset (Fin g.m)) : Prop :=
  (∀ (e : Sym2 (Fin n)) (he : e ∈ t.1) (i j : Fin n) (hij : e = s(i, j)),
      π.1 ⟨i, a i ⟨e, he, by rw [hij]; exact Sym2.mem_mk_left i j⟩⟩ =
        ⟨j, a j ⟨e, he, by rw [hij]; exact Sym2.mem_mk_right i j⟩⟩) ∧
  (∀ r : g.Resid t a, π.1 r.1 = (μ.1 r).1) ∧
  T = Finset.univ.filter (fun k => ¬ g.IsResid t a (g.pairOf π.1 k).1)

open Classical in
/-- The probability that the tilted configuration model (P1)–(P3) outputs the pairing `π`
together with the planted tree `T` (a set of edges of `G(π)`):
`Σ_{(t,a,μ) producing (π,T)} p₁(t) · 1/#(P2 outcomes) · 1/#(P3 outcomes)`. -/
noncomputable def processProb (π : g.Pairing) (T : Finset (Fin g.m)) : ℝ :=
  ∑ t : LTree n, ∑ a : g.Attach t, ∑ μ : PerfMatch (g.Resid t a),
    if g.Produces t a μ π T then
      g.p1 t / ((Fintype.card (g.Attach t) : ℝ) * (Fintype.card (PerfMatch (g.Resid t a)) : ℝ))
    else 0

/-- The law of the pairing `π` (equivalently of `G(π)` with its edge labels) in the tilted
configuration model. -/
noncomputable def pairLaw (π : g.Pairing) : ℝ := ∑ T, g.processProb π T

/-- `P(X = ℓ)`: `X` is the length of the fundamental cycle of a uniformly random non-tree edge
of `(π, T)` drawn from the tilted model (Proposition C.7). -/
noncomputable def cycleLenProb (ℓ : ℕ) : ℝ :=
  ∑ π, ∑ T, g.processProb π T *
    (((Finset.univ.filter (fun e => e ∉ T ∧ (g.graphOf π).cycLen T e = ℓ)).card : ℝ) / g.cr)

/-- `E X^{−1/2}` (Lemma 3.8, Eq. (13), Lemma C.8). -/
noncomputable def EXneg : ℝ :=
  ∑ π, ∑ T, g.processProb π T *
    ((1 / (g.cr : ℝ)) * ∑ e ∈ Finset.univ.filter (fun e => e ∉ T),
      ((g.graphOf π).cycLen T e : ℝ) ^ (-(1 / 2 : ℝ)))

/-- `P(X′ = ℓ)` for the birthday process: draw slots uniformly without replacement; `X′ = ℓ`
iff the first `ℓ` draws lie in distinct groups (vertices) and draw `ℓ + 1` lies in one of
them. The first `ℓ + 1` draws are a uniform injective sequence, each with probability
`1/(α)_{ℓ+1}`. -/
noncomputable def birthdayProb (ℓ : ℕ) : ℝ :=
  ((Finset.univ.filter (fun s : Fin (ℓ + 1) → g.Slot =>
      Function.Injective s ∧
      (∀ j j' : Fin (ℓ + 1), j.1 < ℓ → j'.1 < ℓ → (s j).1 = (s j').1 → j = j') ∧
      ∃ j : Fin (ℓ + 1), j.1 < ℓ ∧ (s (Fin.last ℓ)).1 = (s j).1)).card : ℝ) /
    (g.alpha.descFactorial (ℓ + 1) : ℝ)

/-- `E_G S(K_G)/V(K_G)` over the tilted model, `K_G = Vor(Λ_G)`. -/
noncomputable def ESV : ℝ :=
  ∑ π, g.pairLaw π * (cellSurf (g.graphOf π).voronoiG / cellVol (g.graphOf π).voronoiG)

/-- `E Φ(K_G)` over the tilted model. -/
noncomputable def EPhi : ℝ := ∑ π, g.pairLaw π * Phi (g.graphOf π).voronoiG

end DegSeq

/-- The `q`-regular degree sequence on `n` vertices (`qn` even). -/
def regular (n q : ℕ) (hq : 0 < q) (he : Even (q * n)) : DegSeq n :=
  ⟨fun _ => q, fun _ => hq, by simpa [Finset.sum_const, mul_comm] using he⟩

/-- The `4`-regular degree sequence on `n` vertices (Theorem 1.1 takes `n = d − 1`). -/
def reg4 (n : ℕ) : DegSeq n := regular n 4 (by norm_num) ⟨2 * n, by ring⟩

end FlowLatRound


