-- Prove2me | Definitions.Def_PersistClust_Count_AlgBarcode
-- name    : PersistClust_Count_AlgBarcode
-- status  : Definition
-- author  : @fabianroll
-- created : 2026-10-09T08:57:36.047524+00:00
-- url     : https://prove2.me/theorems/45b7827d-8023-468f-a70c-02be9a470004
-- title:
--   Combinatorial barcode of the upper-star Rips filtration
-- statement:
--   The 0-dimensional persistence barcode of the upper-star Rips filtration $\{R_\delta(L^\alpha)\}_\alpha$ (Eq. (3) of Chazal\u2013Guibas\u2013Oudot\u2013Skraba, INRIA RR-6968, 2009), read off from the union-find sweep of Procedure 1 run with merge threshold $\tau=+\infty$: each neighbouring entry absorbed into the entry of the highest root while vertex $i$ is processed dies at level $g_i$, giving the off-diagonal point $(g_r,g_i)$; surviving entries give the immortal points $(g_r,-\infty)$. This is the standard elder-rule (Kruskal) pairing for an upper-star filtration whose critical values are the $g_i$. The function `ripsBarcode g Dm \delta \sigma` returns the multiplicity of a point $(b,d)\in\overline{\mathbb R}\times\overline{\mathbb R}$; it is independent of the tie-breaking sort order $\sigma$ and coincides pointwise with the analytic diagram `ripsDiagram`.
-- source:
--   Chazal\u2013Guibas\u2013Oudot\u2013Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), \u00a73 (Procedure 1) and \u00a74.2; Eq. (3) for the upper-star Rips filtration; pp. 8\u20139, 17\u201323.

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

namespace PersistClust.Count

noncomputable section

variable {n : ℕ}

/-!
### Combinatorial barcode of the upper-star Rips filtration

The 0-dimensional persistence barcode of the upper-star Rips filtration
$\{R_\delta(L^\alpha)\}_\alpha$ (Eq. (3)) can be read off directly from the union-find
sweep of Procedure 1 run with merge threshold $\tau = +\infty$: every neighbouring entry
that is absorbed into the entry of the highest root dies at the current level $g_i$,
giving an off-diagonal point $(g_r, g_i)$; the entries surviving at the end give the
immortal points $(g_r, -\infty)$. This is the standard elder-rule (Kruskal) pairing for
an upper-star filtration whose critical values are the $g_i$.

`ripsBarcode Dm g δ σ` is this combinatorial multiplicity function. It is independent of
the tie-breaking sort order `σ` (any `IsSortOrder g σ` gives the same function), and it
coincides pointwise with `ripsDiagram Dm g δ` (the analytic diagram defined via `mult`).
-/

/-- One step of the plain (elder-rule, $\tau = +\infty$) persistence sweep at vertex `i`,
carrying the union-find state and the accumulated off-diagonal pair multiplicities.
Deaths are recorded at level `g i`; pairs with `g r = g i` (zero persistence, on the
diagonal) are dropped, matching the convention that the off-diagonal diagram has zero
multiplicity on the diagonal. -/
def barStep (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    : UFState n × ((EReal × EReal) → ℕ∞) :=
  let lab := st.1
  let acc := st.2
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  if S = ∅ then (Function.update lab i (some i), acc)
  else
    let root : Fin n → Fin n := fun j => (lab j).getD j
    let ri := root (firstProcessed σ S i)
    -- at τ = +∞ every neighbouring root is merged, so `M` is all neighbouring roots.
    let M : Finset (Fin n) := insert ri (S.image root)
    let R := firstProcessed σ M ri
    let lab2 : UFState n := fun v =>
      if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none
    -- entries whose root dies at level `g i`; drop zero-persistence (diagonal) deaths.
    let dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal))
    let acc2 : EReal × EReal → ℕ∞ := fun p =>
      acc p + dying.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
    (lab2, acc2)

/-- The full elder-rule sweep state (union-find label map + accumulated off-diagonal
multiplicities) after processing `σ (n-1), …, σ 0`. -/
def barRun (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    : UFState n × ((EReal × EReal) → ℕ∞) :=
  (List.finRange n).reverse.foldl
    (fun st k => barStep g Dm δ σ st (σ k))
    ((fun _ => none), (fun _ => 0))

/-- The combinatorial 0-th persistence barcode of the upper-star Rips filtration: the
multiplicity of a point `(b, d)` is the number of elder-rule pairs with birth `b` and
death `d`, where immortal components contribute to `(b, -∞)`. -/
def ripsBarcode (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    : EReal × EReal → ℕ∞ :=
  let st := barRun g Dm δ σ
  let lab := st.1
  let acc := st.2
  let immortals : Finset (Fin n) := Finset.univ.filter (fun r => lab r = some r)
  fun p => acc p + immortals.sum (fun r => if p = ((g r : EReal), ⊥) then 1 else 0)

end

end PersistClust.Count


