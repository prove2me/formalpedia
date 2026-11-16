-- Prove2me | Definitions.Def_MajorityDepthThree_Exact_Supplement_Constructions
-- name    : MajorityDepthThree_Exact_Supplement_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:16:16.537052+00:00
-- url     : https://prove2.me/theorems/ecdb4a98-4b4f-4186-8f13-fdde8e64c2ed
-- title:
--   Deficit maxima $\Phi_0(s,t)$, disjoint sums and the constructions $P^3_{s,t}$
-- statement:
--   This file builds on the published CNF interface (finite ambient variable set $V$, signed clauses, transversals, the count $\theta_t$ of satisfying sets of size exactly $t$, the $t$-threshold property and the maximum $\Theta(|V|,t,k)$ over all signed valid $t$-threshold CNFs of width at most $k$).
--
--   **Monotone maximum.** For a finite variable set $V$, the number $\Theta^{+}(V,t,k)$ is the maximum of $\theta_t(F)$ over all valid, width-at-most-$k$, $t$-threshold CNFs $F$ on $V$ that are monotone (no negative literals); it is $0$ when no such CNF exists.
--
--   **Deficit parameterization (Definition 3.6).** For an integer $s$ (the deficit) and a natural number $t$, put $n=3t-s$ (read as $0$ if negative) and $V=\{0,\dots,n-1\}$. Then
--
--   $$\Phi_0(s,t)=\Theta^{+}(V,t,3),\qquad \Theta_{\mathrm{def}}(s,t)=\Theta(n,t,3),$$
--
--   the maxima of the number of $t$-transversals over monotone, respectively all signed, $t$-threshold 3-CNFs on $3t-s$ variables.
--
--   **Blocks and sums.** Block CNFs use the natural numbers as variables; a block on $m$ variables uses $0,\dots,m-1$. Shifting a CNF by $o$ adds $o$ to every variable. The disjoint sum $F_1+F_2$, with $F_1$ on $m_1$ variables, is $F_1$ together with $F_2$ shifted by $m_1$; the multiple $\ell\cdot F$ of a CNF on $m$ variables is the union of the copies of $F$ shifted by $0,m,\dots,(\ell-1)m$. The blocks are $K_3^{(3)}=\{\{0,1,2\}\}$; $K_4^{(3)}$, all four 3-subsets of $\{0,1,2,3\}$; $T_5^{(3)}=\{\{0,1,2\},\{2,3,4\},\{0,1,3\}\}$ (the paper's $\{\{1,2,3\},\{3,4,5\},\{1,2,4\}\}$ with every variable lowered by one); and $T_6^{(3)}$ with $x_0,y_0,x_1,y_1,x_2,y_2=0,\dots,5$, the six clauses $\{x_0,y_0,x_1\},\{x_0,y_0,y_1\},\{x_1,y_1,x_2\},\{x_1,y_1,y_2\},\{x_2,y_2,x_0\},\{x_2,y_2,y_0\}$.
--
--   **The construction $P^3_{s,t}$** is the monotone 3-CNF, on the variables $\{0,\dots,3t-s-1\}$,
--
--   $$P^3_{s,t}=\begin{cases} t\cdot K_3^{(3)} & s\le 0,\\ (t-2)\cdot K_3^{(3)}+T_5^{(3)} & s=1,\\ (t-s)\cdot K_3^{(3)}+\tfrac s2\cdot K_4^{(3)} & s \text{ even},\ 2\le s\le t,\\ (t-s)\cdot K_3^{(3)}+\tfrac{s-3}2\cdot K_4^{(3)}+T_6^{(3)} & s\text{ odd},\ 3\le s\le t.\end{cases}$$
--
--   For $s\le0$ the last $-s$ variables are isolated; in the other cases the blocks use exactly $3t-s$ variables.
--
--   These objects carry the paper's §3.3 constructions and the deficit profile of Theorem 3.10.
--
--   **Formalization Note.** Outside the parameter ranges listed above, `P3 s t` is a meaningless value (natural-number subtraction truncates); every theorem using it restricts to those ranges. The case $s=1$ is only meaningful for $t\ge2$.
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), pp.7–9, Definition 3.1, Examples 3.3–3.4, Definition 3.6 and the definition of P^3_{s,t} in Section 3.3

import Definitions.Def_MajorityDepthThree_Exact_CNF

set_option autoImplicit false

namespace MajorityDepthThree.Exact.Supplement

open MajorityDepthThree.Exact

/-! Gurumukhani–Kleber–Paturi–Rosin–Saks–Talebanfard, STOC 2027 submission #677,
pp. 7–9: Definition 3.1, Examples 3.3–3.4, Definition 3.6 and the construction
`P^3_{s,t}` of §3.3. Block CNFs live on the variables `ℕ`; a block on `m` variables
uses exactly the variables `0, …, m - 1`, and the ambient variable set of a CNF built
here is `Finset.range n`. -/

section Maxima

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Valid, width-at-most-`k`, `t`-threshold CNFs on `V` that are moreover monotone. -/
noncomputable def monoCandidates (V : Finset α) (t k : ℕ) : Finset (CNF α) := by
  classical
  exact (candidates V t k).filter (fun F => Monotone F)

/-- The maximum of `θ_t` over the monotone `t`-threshold `k`-CNFs on `V`
(zero if there is none). -/
noncomputable def thetaMaxMono (V : Finset α) (t k : ℕ) : ℕ :=
  (monoCandidates V t k).sup (fun F => theta V F t)

end Maxima

/-- `Φ₀(s,t)` (Definition 3.6): the maximum number of `t`-transversals of a `t`-threshold
monotone 3-CNF on `n = 3t - s` variables. -/
noncomputable def Phi0 (s : ℤ) (t : ℕ) : ℕ :=
  thetaMaxMono (Finset.univ : Finset (Fin (3 * (t : ℤ) - s).toNat)) t 3

/-- `Θ(3t - s, t, 3)`: the maximum over all (signed) `t`-threshold 3-CNFs on `3t - s`
variables, i.e. the base `thetaMax` at deficit `s`. -/
noncomputable def ThetaDeficit (s : ℤ) (t : ℕ) : ℕ :=
  thetaMax (Finset.univ : Finset (Fin (3 * (t : ℤ) - s).toNat)) t 3

/-- Shift every variable of a clause by `o`. -/
def shiftClause (o : ℕ) (c : Clause ℕ) : Clause ℕ :=
  (c.1.map (addRightEmbedding o), c.2.map (addRightEmbedding o))

/-- Shift every variable of a CNF by `o`. -/
def shift (o : ℕ) (F : CNF ℕ) : CNF ℕ := F.image (shiftClause o)

/-- Disjoint sum `F₁ + F₂`: `F₁` on the variables `0, …, m₁ - 1` and a copy of `F₂`
placed on the variables `m₁, m₁ + 1, …`. -/
def disjSum (m₁ : ℕ) (F₁ F₂ : CNF ℕ) : CNF ℕ := F₁ ∪ shift m₁ F₂

/-- `ℓ · F`: `ℓ` disjoint copies of a CNF `F` on `m` variables, copy `j` on the
variables `j m, …, j m + m - 1`. -/
def copies (ℓ m : ℕ) (F : CNF ℕ) : CNF ℕ :=
  (Finset.range ℓ).biUnion (fun j => shift (j * m) F)

/-- The monotone clause with positive variable set `S`. -/
def posClause (S : Finset ℕ) : Clause ℕ := (S, ∅)

/-- `K₃^{(3)} = {{1,2,3}}` on the variables `0,1,2`. -/
noncomputable def K3 : CNF ℕ := clique (Finset.range 3) 3

/-- `K₄^{(3)}`: all four 3-subsets of the variables `0,1,2,3`. -/
noncomputable def K4 : CNF ℕ := clique (Finset.range 4) 3

/-- `T₅^{(3)} = {{1,2,3},{3,4,5},{1,2,4}}` (Example 3.3), variables `1,…,5` renamed
`0,…,4`. -/
def T5 : CNF ℕ :=
  {posClause {0, 1, 2}, posClause {2, 3, 4}, posClause {0, 1, 3}}

/-- `T₆^{(3)}` (Example 3.4) with `x₀,y₀,x₁,y₁,x₂,y₂ = 0,1,2,3,4,5`:
`{x₀,y₀,x₁}, {x₀,y₀,y₁}, {x₁,y₁,x₂}, {x₁,y₁,y₂}, {x₂,y₂,x₀}, {x₂,y₂,y₀}`. -/
def T6 : CNF ℕ :=
  {posClause {0, 1, 2}, posClause {0, 1, 3}, posClause {2, 3, 4},
   posClause {2, 3, 5}, posClause {4, 5, 0}, posClause {4, 5, 1}}

/-- `P^3_{s,t}` (§3.3, p. 9), a monotone 3-CNF on the variables `range (3t - s)`:
* `t · K₃` if `s ≤ 0` (the remaining `-s` variables are isolated);
* `(t - 2) · K₃ + T₅` if `s = 1`;
* `(t - s) · K₃ + (s/2) · K₄` if `s` is even, `2 ≤ s ≤ t`;
* `(t - s) · K₃ + ((s - 3)/2) · K₄ + T₆` if `s` is odd, `3 ≤ s ≤ t`.
Outside these parameter ranges the value carries no meaning. -/
noncomputable def P3 (s : ℤ) (t : ℕ) : CNF ℕ :=
  if s ≤ 0 then copies t 3 K3
  else if s = 1 then disjSum (3 * (t - 2)) (copies (t - 2) 3 K3) T5
  else if s % 2 = 0 then
    disjSum (3 * (t - s.toNat)) (copies (t - s.toNat) 3 K3) (copies (s.toNat / 2) 4 K4)
  else
    disjSum (3 * (t - s.toNat)) (copies (t - s.toNat) 3 K3)
      (disjSum (4 * ((s.toNat - 3) / 2)) (copies ((s.toNat - 3) / 2) 4 K4) T6)

end MajorityDepthThree.Exact.Supplement


