-- Prove2me | Definitions.Def_OptInapprox_MaxCut_ReductionGraph
-- name    : OptInapprox_MaxCut_ReductionGraph
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-11-05T14:39:38.073919+00:00
-- url     : https://prove2.me/theorems/c0f4cda0-c330-40e3-96db-ebf67b65e631
-- title:
--   §8.1, pp. 18–19 — the weighted MAX-CUT instance of the Unique Label Cover → MAX-CUT reduction (noise ρ = −p/q, R table copies)
-- statement:
--   The weighted MAX-CUT instance produced from a Unique Label Cover instance $\mathcal L(V,W,E,[M],\{\sigma_{v,w}\})$ by the PCP verifier of §8.1, with natural-number edge weights as allowed in §7.1.
--
--   **Parameters.** $R\ge 1$ (number of copies of each Long Code table), $K$ (weight scale) and $p\le q$, $q>0$, so that the noise rate is $\rho=-p/q$.
--
--   **Vertices.** The triples $(w,r,x)$ with $w\in W$, $r<R$ and $x\in\{-1,1\}^M$, i.e. $R$ copies of the Long Code table of every $w\in W$; they are numbered $(wR+r)2^M+\mathrm{code}(x)$ with $\mathrm{code}(x)=\sum_i [x_i=\mathrm{TRUE}]\,2^i$ (`cubeEquiv`).
--
--   **Edges.** For every $v\in V$, every two neighbours $w,w'$ of $v$, every $r,r'<R$ and every $x,\mu\in\{-1,1\}^M$ there is an edge between
--   $$(w,\,r,\,x\circ\sigma_{v,w})\quad\text{and}\quad(w',\,r',\,(x\circ\sigma_{v,w'})\mu)$$
--   of multiplicity
--   $$\Big\lfloor \frac{K\,|W|}{\deg v}\Big\rfloor\cdot\prod_{i=1}^M (q\mp p),$$
--   with $q+p$ for a coordinate $\mu_i=-1$ and $q-p$ for $\mu_i=1$ (so the second factor is $(2q)^M$ times the verifier's probability of $\mu$). Self-loops, which arise exactly when $w=w'$, $r=r'$ and $\mu=\mathbf 1$ and which no cut can cut, are omitted. The edge list is ordered lexicographically by $(v,w,w',r,r',x,\mu)$.
--
--   The cut value of a partition is then (up to the omitted self-loops) the acceptance probability of the verifier "pick $v$, then $w,w'$ uniformly among the neighbours of $v$, $x$ uniform, $\mu$ $\rho$-biased, accept iff $f_w(x\circ\sigma_{v,w})\neq f_{w'}((x\circ\sigma_{v,w'})\mu)$", where $v$ is drawn with probability proportional to $\lfloor K|W|/\deg v\rfloor\deg(v)^2$; hence the edge $(v,w)$ is drawn with probability proportional to $\lfloor K|W|/\deg v\rfloor\deg v\in(K|W|-|W|,\,K|W|]$, i.e. nearly uniformly.
--
--   **Relation to the paper.** In the paper the Label Cover instance is assumed regular on the $V$ side (§8.1, using [38]); then all weights $\lfloor K|W|/\deg v\rfloor$ are equal and, for $R=1$, the instance is exactly the paper's. The $V$-dependent integer weights and the $R$ copies are formalization devices: the weights remove the regularity assumption (at the cost of a factor $K/(K-1)$ in the soundness analysis), and the copies make the omitted self-loops a fraction at most $1/R$ of the total weight. The lemma `rgEdges_loopless` certifies that the edge list has no self-loops.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), §8.1 (the PCP verifier, pp. 18–19) and §7.1 (weighted MAX-CUT); the integer weights and table copies are formalization devices described in the statement

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

namespace OptInapprox.MaxCut

noncomputable section

/-- The enumeration of the cube `{-1,1}^M` (points `Fin M → Bool`) by `Fin (2^M)`: the point `x`
gets the number `∑ᵢ [x i] 2^i` (TRUE contributes the bit `1`). -/
def cubeEquiv (M : ℕ) : (Fin M → Bool) ≃ Fin (2 ^ M) :=
  (Equiv.arrowCongr (Equiv.refl (Fin M)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The MAX-CUT vertex `(w, r, x)`: the point `x` of the `r`-th copy of the Long Code table of
`w ∈ W`, numbered `(w * R + r) * 2^M + code(x)`. -/
def rgVertex (L : ULC) (R : ℕ) (w : Fin L.nW) (r : Fin R) (x : Fin L.M → Bool) :
    Fin (L.nW * R * 2 ^ L.M) :=
  finProdFinEquiv (finProdFinEquiv (w, r), cubeEquiv L.M x)

/-- The numerator of the noise weight of `μ` for `ρ = -p/q`: `∏ᵢ (q ± p)`, with `q + p` for a
TRUE (`-1`) coordinate and `q - p` for a FALSE (`1`) coordinate; `muWeight (-p/q) μ` equals
`muNum p q μ / (2q)^M`. -/
def muNum (p q : ℕ) {M : ℕ} (μ : Fin M → Bool) : ℕ :=
  ∏ i, if μ i then q + p else q - p

/-- The integer weight `⌊K · |W| / deg(v)⌋` attached to the tests through the vertex `v ∈ V`
(approximately proportional to `1/deg(v)`, so that the edge `(v, w)` is picked nearly
uniformly). -/
def rgWeight (L : ULC) (K : ℕ) (v : Fin L.nV) : ℕ :=
  K * L.nW / (L.nbrs v).card

/-- The weighted edge list of the MAX-CUT instance produced from the Unique Label Cover instance
`L` by the PCP verifier of §8.1 with `ρ = -p/q` (Long Code tables of the `W`-vertices, each
repeated `R` times): for every `v ∈ V`, neighbours `w, w'` of `v`, copies `r, r' < R`, `x` and
`μ` in the cube, the edge between `(w, r, x ∘ σ_{v,w})` and `(w', r', (x ∘ σ_{v,w'}) μ)` with
multiplicity `rgWeight v * muNum μ`; self-loops (which no cut can cut) are omitted. -/
def rgEdges (L : ULC) (R K p q : ℕ) :
    List (Fin (L.nW * R * 2 ^ L.M) × Fin (L.nW * R * 2 ^ L.M)) :=
  (List.finRange L.nV).flatMap fun v =>
  (List.finRange L.nW).flatMap fun w =>
  (List.finRange L.nW).flatMap fun w' =>
  if (v, w) ∈ L.E ∧ (v, w') ∈ L.E then
    (List.finRange R).flatMap fun r => (List.finRange R).flatMap fun r' =>
    (List.finRange (2 ^ L.M)).flatMap fun a => (List.finRange (2 ^ L.M)).flatMap fun b =>
      if rgVertex L R w r (compose ((cubeEquiv L.M).symm a) (L.σ v w)) =
          rgVertex L R w' r' (coordMul (compose ((cubeEquiv L.M).symm a) (L.σ v w'))
            ((cubeEquiv L.M).symm b)) then []
      else List.replicate (rgWeight L K v * muNum p q ((cubeEquiv L.M).symm b))
        (rgVertex L R w r (compose ((cubeEquiv L.M).symm a) (L.σ v w)),
          rgVertex L R w' r' (coordMul (compose ((cubeEquiv L.M).symm a) (L.σ v w'))
            ((cubeEquiv L.M).symm b)))
  else []

theorem rgEdges_loopless (L : ULC) (R K p q : ℕ) : ∀ e ∈ rgEdges L R K p q, e.1 ≠ e.2 := by
  intro e he
  simp only [rgEdges, List.mem_flatMap, List.mem_finRange, true_and] at he
  obtain ⟨v, w, w', he⟩ := he
  split_ifs at he with h1
  · simp only [List.mem_flatMap, List.mem_finRange, true_and] at he
    obtain ⟨r, r', a, b, he⟩ := he
    split_ifs at he with h2
    · simp at he
    · rw [List.mem_replicate] at he
      rw [he.2]
      exact h2
  · simp at he

/-- The weighted MAX-CUT instance of §8.1 built from the Unique Label Cover instance `L`
(parameters: `R` copies of each Long Code table, weight scale `K`, noise rate `ρ = -p/q`). -/
def reductionGraph (L : ULC) (R K p q : ℕ) : WMaxCut :=
  ⟨L.nW * R * 2 ^ L.M, rgEdges L R K p q, rgEdges_loopless L R K p q⟩

end

end OptInapprox.MaxCut


