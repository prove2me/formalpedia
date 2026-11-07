-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_levelsBC
-- name    : QAdvFew_PoQOracle_levelsBC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:40.900284+00:00
-- url     : https://prove2.me/theorems/1d3acc24-2a60-4737-9cbd-d1af670b555e
-- title:
--   The levels $B_t$, $C_t$
-- statement:
--   The levels $(B_t,C_t)$ are defined by strong recursion on $t$. Level $t$ is built from the oracle $O'$ that answers queries to levels $m\le\lfloor\sqrt t\rfloor$, $m<t$, of $A$, $B$, $C$, and every other query with $0$.
--
--   - For a code of a pair $(M,x)$ with fewer than $t$ bits, the function $B_t((M,x),\cdot):\{0,1\}^{t^2}\to\{0,1\}$ is the $\mathcal F_{2^{t^2}}$ seed of that pair if $M^{O'}(x)$ accepts, and otherwise its uniform seed.
--   - $C_t(M,x)=1$ if the nondeterministic machine accepts, and $0$ otherwise.
--
--   Shorter queries are read as padded to $t$ bits. The parameter `cut` selects the distribution: $\mathcal F$-seeds are used exactly at the levels $t<$ `cut`, so `cut` $=\infty$ gives $\mathcal D$ and `cut` $=n$ gives $\mathcal D^{(n)}$.
--
--   **Formalization Note** The restriction "$M$ queries only $\mathcal O_1,\dots,\mathcal O_{\lfloor\sqrt t\rfloor}$" is read as truncating the oracle, which makes the recursion well-founded and gives the same value on a machine obeying it.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24); §4.4, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Seed
import Definitions.Def_QAdvFew_PoQOracle_unpad
import Definitions.Def_QAdvFew_PoQOracle_psAccepts
import Definitions.Def_QAdvFew_PoQOracle_npAccepts
import Definitions.Def_QAdvFew_PoQOracle_codePair
import Definitions.Def_QAdvFew_PoQOracle_forrOracle
import Definitions.Def_QAdvFew_PoQOracle_affineOracle
import Definitions.Def_QAdvFew_PoQOracle_join3

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

open Classical in
/-- Level `t` of `B` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, §4.1, p. 22 (PDF p. 24)), given the oracle `O'` of the levels
`≤ ⌊√t⌋`. A query is padded with zeros; its first `t` bits, unpadded, are a code `c`, and its next
`t²` bits an argument `y`. If `c` is the code of a pair `(M, x)` and `M^{O'}(x)` accepts within
`2^t` steps and `t` cells, `B_t((M, x), y)` is bit `y` of the `F_{2^{t²}}` seed of `(t, c)` (when
`useF`); otherwise it is bit `y` of the uniform seed of `(t, c)`. A query whose code is not the code
of a pair is answered `0`. -/
noncomputable def bLevel (t : ℕ) (O' : Oracle) (useF : Bool)
    (Fs Us : Str → Fin (2 ^ (t ^ 2)) → Bool) : Oracle := fun q =>
  let q' := q ++ List.replicate (t + t ^ 2) false
  let c := unpad (q'.take t)
  let y := (q'.drop t).take (t ^ 2)
  if (∃ (M : OTM) (x : Str), codePair M x = c) then
    let seed := if useF ∧ (∃ (M : OTM) (x : Str), codePair M x = c ∧ psAccepts M O' x t)
      then Fs c else Us c
    if h : binVal y < 2 ^ (t ^ 2) then seed ⟨binVal y, h⟩ else false
  else false

open Classical in
/-- Level `t` of `C` (§4.1, p. 22 (PDF p. 24): "`C_t(M, x) = 1` if `M^O(x)` accepts, `0`
otherwise"), given the oracle `O'` of the levels `≤ ⌊√t⌋`: the query, padded to `t` bits and
unpadded, is a code `c`; the answer is `1` iff `c` is the code of a pair `(V, x)` with
`npAccepts V O' x t`. -/
noncomputable def cLevel (t : ℕ) (O' : Oracle) : Oracle := fun q =>
  let c := unpad ((q ++ List.replicate t false).take t)
  decide (∃ (V : OTM) (x : Str), codePair V x = c ∧ npAccepts V O' x t)

/-- The levels `(B_t, C_t)` of a sample, by strong recursion on `t` (§4.1, pp. 21–22 (PDF
pp. 23–24): "`B_t` and `C_t` will be defined inductively"; "`M` queries only the oracles
`{O_1, …, O_{⌊√t⌋}}`"). Level `t` is built from the oracle `O'` that answers queries to levels
`m ≤ ⌊√t⌋`, `m < t`, of `A`, `B`, `C` as the sample does, and every other query with `0`. The
`F`-seed is used at level `t` iff `t < cut`: `cut = ⊤` gives `D`, `cut = n` gives `D^(n)` (p. 24:
"For `t ≥ n` … always sample `B_t((M, x), ·)` from the uniform distribution").

**Formalization Note** The restriction "queries only `O_1, …, O_{⌊√t⌋}`" is read as truncation:
`M` runs with the truncated oracle `O'`. For `t ≥ 2`, `⌊√t⌋ < t`; for `t ≤ 1` no pair has a code of
length `< t`, so these levels have no members. -/
noncomputable def levelsBC (cut : ℕ∞) (ω : Seed) : ℕ → Oracle × Oracle := fun t =>
  Nat.strongRecOn t fun t ih =>
    let k := Nat.sqrt t
    let lev : ℕ → Oracle × Oracle := fun m =>
      if h : m < t ∧ m ≤ k then ih m h.1 else (fun _ => false, fun _ => false)
    let O' := join3 (join fun m => if m ≤ k then affLevel m (roOf ω m) else fun _ => false)
      (join fun m => (lev m).1) (join fun m => (lev m).2)
    (bLevel t O' (decide ((t : ℕ∞) < cut)) (fun c => ω.2.1 (t, c)) (fun c => ω.2.2 (t, c)),
      cLevel t O')

end QAdvFew.PoQOracle


