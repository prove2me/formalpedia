-- Prove2me | Definitions.Def_TightClock_Supplement_maxSample
-- name    : TightClock_Supplement_maxSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:08:46.761344+00:00
-- url     : https://prove2.me/theorems/95bbacc0-9d52-40cf-972c-2dd192f8c7cf
-- title:
--   Auction 1 — $\mathrm{MaxSample}$
-- statement:
--   **Auction 1 (MaxSample)** on disjoint groups $G_1,\dots,G_k$. Each bidder is sampled independently with probability $3/8$ (sample $T$), and no offers are made at this step. For each group $G_j$ the auction keeps the active sampled bidders $A_j=T\cap G_j$, a common price $a_j=0$, the dropped total $L_j=0$ and the running total $C_j=L_j+a_j|A_j|$. Let $G=\{j:A_j\ne\emptyset\}$. While $|G|>1$:
--
--   1. choose $j'\in\arg\min_{j\in G}C_j$ (ties by the selection rule);
--   2. $a_{j'}\leftarrow a_{j'}+\delta$, offered to every member of $A_{j'}$; let $E$ be those who reject;
--   3. $L_{j'}\leftarrow L_{j'}+(a_{j'}-\delta)|E|$, $A_{j'}\leftarrow A_{j'}\setminus E$, and remove $j'$ from $G$ if $A_{j'}=\emptyset$.
--
--   Finally run $\mathrm{RetainOnly}(G_j)$ for the unique $j\in G$, or $\mathrm{RetainOnly}(G_1)$ for a fixed group if no bidder was sampled. Unsampled bidders stay active at price $0$ throughout.
--
--   **Formalization Note** The sample is $T=\{i:u_i<3/8\}$ for independent uniforms $u_i$ on $[0,1]$. $G$ is recomputed as $\{j:A_j\ne\emptyset\}$ at each iteration, which is the page's $G$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.1, Auction 1, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_TightClock_Supplement_retainOnly
import Definitions.Def_TightClock_Supplement_Selector

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 1, `MaxSample`, on disjoint groups `Gs`. Each bidder is sampled independently with
probability `3/8` (bidder `i` is sampled iff `uᵢ < 3/8`), with no offers. For each group `G` the
auction keeps the active sampled bidders `A_G` (initially `T ∩ G`), a common price `a_G = 0`, the
dropped total `L_G = 0`, and the running total `C_G = L_G + a_G |A_G|`. While more than one group has
active sampled bidders, it chooses `j′ ∈ arg min C_G` among them (chosen by the selection rule `sel`), raises
`a_{j′}` by `δ`, offers it to every member of `A_{j′}`, adds `(a_{j′} − δ)|E|` to `L_{j′}` for the set
`E` of those who reject, and removes `E` from `A_{j′}`. Finally it runs `RetainOnly(G_j)` for the
unique remaining group, or `RetainOnly(G₁)` (a fixed group, chosen by `sel`) if no bidder was
sampled. Unsampled bidders stay at price `0` throughout. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4.1, Auction 1, p.16 (PDF 19).

**Formalization Note** The set `G = {j : A_j ≠ ∅}` of the page is recomputed at each iteration; it
equals the page's `G`, which removes `j′` exactly when `A_{j′}` becomes empty. Offers within a step
go in the order of `Fin n`. -/
noncomputable def maxSample {n : ℕ} (δ : ℝ) (Gs : Finset (Finset (Fin n))) (sel : Selector n)
    (u : Fin n → unitInterval) : ClockProg n (Finset (Fin n)) := do
  let T : Finset (Fin n) := Finset.univ.filter (fun i => (u i : ℝ) < 3 / 8)
  let runTotal : (Finset (Fin n) → ℝ) → (Finset (Fin n) → ℝ) → (Finset (Fin n) → Finset (Fin n)) →
      Finset (Fin n) → ℝ := fun a L A G => L G + a G * (A G).card
  let (st, _, _, A) ← ClockProg.loop
    (fun s : CState n × (Finset (Fin n) → ℝ) × (Finset (Fin n) → ℝ) × (Finset (Fin n) → Finset (Fin n)) => do
      let (st, a, L, A) := s
      let Gact := Gs.filter (fun G => (A G).Nonempty)
      if 1 < Gact.card then
        let j := sel.pick Gact (fun G => - runTotal a L A G)
        let price := a j + δ
        let (st', E) ← ((List.finRange n).filter (fun i => decide (i ∈ A j))).foldlM
          (fun (acc : CState n × Finset (Fin n)) i => do
            let (b, st') ← offerTo acc.1 i price
            return (st', if b then acc.2 else insert i acc.2)) (st, ∅)
        return Sum.inl (st', Function.update a j price,
          Function.update L j (L j + (price - δ) * E.card), Function.update A j (A j \ E))
      else return Sum.inr s)
    (⟨fun _ => 0, Finset.univ⟩, fun _ => 0, fun _ => 0, fun G => T ∩ G)
  let Gact := Gs.filter (fun G => (A G).Nonempty)
  if Gact.Nonempty then retainOnly δ st (sel.pick Gact (fun _ => 0))
  else retainOnly δ st (sel.pick Gs (fun _ => 0))

end TightClock.Supplement


