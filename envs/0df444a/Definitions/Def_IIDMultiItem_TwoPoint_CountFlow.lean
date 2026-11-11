-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_CountFlow
-- name    : IIDMultiItem_TwoPoint_CountFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:54.239941+00:00
-- url     : https://prove2.me/theorems/f9d80166-6ee2-41d7-8b5c-21a4924e21dc
-- title:
--   The flow (3.7) of §3.3 for one buyer, rules (a)–(c) of §B.2
-- statement:
--   Fix buyer $i$ and the others' reports, with $H$, $D=[m]\setminus H$ and $d=|D|$ as in §3.2. A report $S$ splits as $Q=S\cap H$ and $T=S\cap D$, $r=|T|$. Let $f_H(Q)=q^{|Q|}p^{|H|-|Q|}$ and $R\sim\mathrm{Bin}(d,q)$. The flow puts weight only on downward IC constraints that delete one element and on the IR constraint of $\emptyset$:
--
--   * (a) for $T\ne\emptyset$ with $|T|=r$ and $j\in T$: $\displaystyle\lambda(Q\cup T,\,Q\cup T\setminus\{j\})=\frac{f_H(Q)\Pr[R\ge r]}{r\binom dr}$; (3.7)
--   * (b) processing the nonempty $Q\subseteq H$ in decreasing order of cardinality, for $j\in Q$: $\displaystyle\lambda(Q,Q\setminus\{j\})=\frac1{|Q|}\Big(f_H(Q)+\sum_{j'\in H\setminus Q}\lambda(Q\cup\{j'\},Q)\Big)$;
--   * (c) all other edges have weight $0$; $\lambda(\emptyset,\bot)=f(\emptyset)+\sum_{j\in[m]}\lambda(\{j\},\emptyset)$ and $\lambda(S,\bot)=0$ for $S\ne\emptyset$.
--
--   The flow depends on the buyer and the others' reports only through $H$.
--
--   **Formalization Note.** `countFlow p m H` is the flow for the set `H`; `countIC p H S' S` $=\lambda(S',S)$. Rule (a) is `weightD p H S'` with $Q=S'\cap H$, $r=|S'\setminus H|$, $d=|[m]\setminus H|$. Rule (b) is written through the mass $\mathrm{mass}(Q)=f_H(Q)+\sum_{j'\in H\setminus Q}\lambda(Q\cup\{j'\},Q)$ held by $Q$, so that $\lambda(Q,Q\setminus\{j\})=\mathrm{mass}(Q)/|Q|$; `massAux p H k Q` unfolds the recursion $k$ levels and `mass p H Q = massAux p H |H \ Q| Q`, which stops at $Q=H$.
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 15 (PDF 17), §3.3, (3.7); p. 37 (PDF 39), §B.2 (a)–(c)

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Flow
import Definitions.Def_IIDMultiItem_TwoPoint_Counts

open scoped BigOperators

/-!
# The flow of §3.3 for one buyer

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §3.3, p. 15, (3.7); §B.2 rules (a)–(c), p. 37.

Fix buyer `i` and the others' reports; the flow depends on them only through the set `H` of items
some opponent reports high. `D = [m] \ H`, `d = |D|`, a report `S` splits as `Q = S ∩ H` and
`T = S ∩ D = S \ H`, `r = |T|`, `f_H(Q) = q^{|Q|} p^{|H|−|Q|}`, `R ∼ Bin(d, q)`.

* (a) for `T ≠ ∅` and `j ∈ T`: `λ(Q ∪ T, Q ∪ T \ {j}) = f_H(Q) Pr[R ≥ r] / (r · C(d, r))`;
* (b) for nonempty `Q ⊆ H`, in decreasing order of `|Q|`, and `j ∈ Q`:
  `λ(Q, Q \ {j}) = (1/|Q|)(f_H(Q) + ∑_{j' ∈ H \ Q} λ(Q ∪ {j'}, Q))`;
* (c) every other edge has weight `0`; `λ(∅, ⊥) = f(∅) + ∑_j λ({j}, ∅)`, `λ(S, ⊥) = 0` for
  `S ≠ ∅`.

Rule (b) is written through the mass `mass Q = f_H(Q) + ∑_{j' ∈ H \ Q} λ(Q ∪ {j'}, Q)` that `Q`
holds, so that `λ(Q, Q \ {j}) = mass Q / |Q|`; `massAux k Q` unfolds the recursion `k` levels,
and `mass Q = massAux |H \ Q| Q` (the recursion stops at `Q = H`).
-/

namespace IIDMultiItem.TwoPoint

open Classical

variable {m : ℕ}

/-- `f_H(Q) = q^{|Q|} p^{|H|−|Q|}`, `q = 1 − p`. -/
def fH (p : ℝ) (H Q : Finset (Fin m)) : ℝ :=
  (1 - p) ^ Q.card * p ^ (H.card - Q.card)

/-- Rule (a): the weight `f_H(Q) Pr[R ≥ r] / (r · C(d, r))` of each edge deleting one element of
`T` from the report `S' = Q ∪ T` (`Q = S' ∩ H`, `r = |S' \ H|`, `d = |[m] \ H|`, `R ∼ Bin(d, q)`). -/
noncomputable def weightD (p : ℝ) (H S' : Finset (Fin m)) : ℝ :=
  fH p H (S' ∩ H) * binGe (Finset.univ \ H).card (1 - p) (S' \ H).card /
    (((S' \ H).card : ℝ) * ((Finset.univ \ H).card.choose (S' \ H).card : ℝ))

/-- The recursion of rule (b), unfolded `k` levels:
`massAux (k + 1) Q = f_H(Q) + ∑_{j' ∈ H \ Q} massAux k (Q ∪ {j'}) / |Q ∪ {j'}|`. -/
noncomputable def massAux (p : ℝ) (H : Finset (Fin m)) : ℕ → Finset (Fin m) → ℝ
  | 0, Q => fH p H Q
  | k + 1, Q => fH p H Q +
      ∑ j' ∈ H \ Q, massAux p H k (insert j' Q) / ((insert j' Q).card : ℝ)

/-- The mass held by `Q ⊆ H` (its own `f_H(Q)` plus all flow entering it along edges of rule (b)). -/
noncomputable def mass (p : ℝ) (H Q : Finset (Fin m)) : ℝ :=
  massAux p H (H \ Q).card Q

/-- The IC weights `λ(S', S)` of rules (a)–(c): nonzero only on edges deleting one element `j`
from `S'`; rule (a) when `j ∈ D`, rule (b) when `j ∈ H` and `S' ⊆ H`, and `0` otherwise. -/
noncomputable def countIC (p : ℝ) (H S' S : Finset (Fin m)) : ℝ :=
  if S ⊆ S' ∧ (S' \ S).card = 1 then
    (if Disjoint (S' \ S) H then weightD p H S'
     else if S' ⊆ H then mass p H S' / (S'.card : ℝ) else 0)
  else 0

/-- The flow (3.7) / §B.2 (a)–(c) for a buyer whose opponents report the items of `H` high:
`λ(S', S) = countIC`, `λ(∅, ⊥) = f(∅) + ∑_j λ({j}, ∅)` and `λ(S, ⊥) = 0` for `S ≠ ∅`. -/
noncomputable def countFlow (p : ℝ) (m : ℕ) (H : Finset (Fin m)) : Flow (Finset (Fin m)) where
  ic S' S := countIC p H S' S
  ir S := if S = ∅ then setPmf p m ∅ + ∑ j : Fin m, countIC p H {j} ∅ else 0

end IIDMultiItem.TwoPoint


