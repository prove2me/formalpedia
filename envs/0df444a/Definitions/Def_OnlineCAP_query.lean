-- Prove2me | Definitions.Def_OnlineCAP_query
-- name    : OnlineCAP_query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:47.75268+00:00
-- url     : https://prove2.me/theorems/da80f44a-d17d-4639-8f01-a6d8f1cab70b
-- title:
--   The query Q_t of Algorithm 2
-- statement:
--   For a fractional vector $x$ on $P$ and a request $R\subseteq P$ (the trace of a bottomless rectangle), let $A(R)$ be the active copies of points of $R$. Let $v$ be the deepest node of the range tree whose interval contains the x-ranks of all points of $R$. The **query** is
--   $$Q=\begin{cases}A(R),& v\text{ a leaf},\\ \text{the larger of } A(R)\cap\pi^{-1}(S_{v_\ell})\text{ and } A(R)\cap\pi^{-1}(S_{v_r}),& \text{otherwise},\end{cases}$$
--   with the left piece on ties, and $Q=\emptyset$ if $R=\emptyset$. Concretely, with $lo,hi$ the least and largest rank of a point of $R$, $v=(h,j)$ where $h$ is the least level with $\lfloor lo/2^h\rfloor=\lfloor hi/2^h\rfloor$ and $j=\lfloor lo/2^h\rfloor$.
--
--   **Formalization Note** The node is located from the points of $R\cap P$, which the algorithm sees, rather than from the endpoints $a_t,b_t$ of the rectangle; the paper takes $a_t,b_t$ to be x-coordinates of points of $P$ without loss of generality (p.17), and both choices give a node whose children separate the points of $R$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Algorithm 2, lines 8–13, p.18; §4.1.2, p.17

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_zvec
import Definitions.Def_OnlineCAP_acount
import Definitions.Def_OnlineCAP_active
import Definitions.Def_OnlineCAP_activeOn
import Definitions.Def_OnlineCAP_xrank
import Definitions.Def_OnlineCAP_nodeSet

namespace OnlineCAP

/-- **The query `Q_t` of Algorithm 2.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Algorithm 2, lines 8–13, p.18 (PDF p.18) and §4.1.2,
p.17: "we consider the deepest node v in the range tree that contains the interval [at, bt] … If v
is a leaf, we simply use At(Rt) directly. Otherwise, letting the two child nodes of v be vℓ and vr,
we consider the sets Rt ∩ P ∩ Svℓ and Rt ∩ P ∩ Svr, construct the corresponding sets of active
copies Aleft_t, Aright_t, and pick the one with larger number of points."

For a fractional vector `x` on `P` and a request `R ⊆ P`: let `lo` and `hi` be the least and the
largest x-rank of a point of `R`; the deepest node containing both is `(h, j)` with `h` the least
level at which `⌊lo / 2^h⌋ = ⌊hi / 2^h⌋` and `j = ⌊lo / 2^h⌋`. If `h = 0` (a leaf) the query is
`A(R)`; otherwise it is the larger of `A(R) ∩ π⁻¹(S_{(h−1, 2j)})` and
`A(R) ∩ π⁻¹(S_{(h−1, 2j+1)})`, the left one on ties. If `R` is empty the query is empty.

**Formalization Note.** The node is located from the ranks of the points of `R ∩ P`, which the
algorithm sees, instead of from the endpoints `a_t, b_t` (the paper assumes w.l.o.g. that they are
x-coordinates of points of `P`, p.17). The level is a natural-number `sInf`; its set is never
empty (at `h = lo + hi` both quotients are `0`), so it is a genuine least element. -/
noncomputable def query (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) (R : Set ↥P) :
    Finset (VirtualPt P) := by
  classical
  exact
    let rs : Finset ℕ := (Finset.univ.filter (fun p : ↥P => p ∈ R)).image (fun p => xrank P p.1.1)
    if hrs : rs.Nonempty then
      let lo := rs.min' hrs
      let hi := rs.max' hrs
      let h := sInf {h : ℕ | lo / 2 ^ h = hi / 2 ^ h}
      let j := lo / 2 ^ h
      if h = 0 then activeOn P x R
      else
        let QL := (activeOn P x R).filter (fun e => e.1 ∈ nodeSet P (h - 1) (2 * j))
        let QR := (activeOn P x R).filter (fun e => e.1 ∈ nodeSet P (h - 1) (2 * j + 1))
        if QR.card ≤ QL.card then QL else QR
    else ∅

end OnlineCAP


