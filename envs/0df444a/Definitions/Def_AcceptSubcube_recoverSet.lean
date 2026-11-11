-- Prove2me | Definitions.Def_AcceptSubcube_recoverSet
-- name    : AcceptSubcube_recoverSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:50.119093+00:00
-- url     : https://prove2.me/theorems/ba10062d-aad6-48c6-af2d-53f03a5a3711
-- title:
--   The recovery procedure of Lemma 3.3
-- statement:
--   Let $\mathcal I$ be an instance on $m$ variables, $\ell\ge2$, $1\le b\le m^\ell$, and fix an orientation rule. If $m<\ell$ the procedure outputs all $2^m$ assignments. Otherwise let $s$ be the largest integer with $s^\ell b\le m^\ell$ (that is, $s=\lfloor m/u\rfloor$ with $u=b^{1/\ell}$) and draw a uniformly random $s$-set $S\subseteq[m]$. Then:
--
--   1. the **seeds** are the assignments to $S$ of induced cost at most $8$;
--   2. for every $i\notin S$, $F_{S\cup\{i\}}$ is the family of assignments to $S\cup\{i\}$ of induced cost at most $16$, oriented by the rule;
--   3. for every seed $z$ and $i\notin S$, $x_i$ is predicted from $(z,0)$ and $(z,1)$: if exactly one lies in $F_{S\cup\{i\}}$, that one; if both do, the head of the edge of direction $i$; if neither does, $0$;
--   4. the output contains, for every seed $z$, the candidate equal to $z$ on $S$ and to the predictions off $S$.
--
--   The file also defines the possible draws (all $s$-subsets of $[m]$), $C_\ell=8(v_\ell(16)+\ell+1)$ and the radius $\min\{m,\lceil C_\ell b^{1/\ell}\rceil\}$ of (3).
--
--   **Formalization Note** The output is a set of assignments (equal candidates from different seeds coincide). Seeds vanish off $S$. The family is passed to the rule in a canonical order, as a function of $(T,F_T)$ only.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §3.3, pp.12–13 (the procedure; (3))

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_FK
import Definitions.Def_AcceptSubcube_GoodOrient

namespace AcceptSubcube

/-- All `2^d` patterns of length `d`, in the order of their index `Σ_i 2^i y_i` (a canonical,
lexicographic encoding of a family, p.12). -/
def allPatterns (d : ℕ) : List (List Bool) :=
  (List.range (2 ^ d)).map (fun j => (List.range d).map (Nat.testBit j))

/-- A pattern `y` on the sorted coordinate list `T`, read as an assignment (`false` off `T`). -/
def listAsg (T : List ℕ) (y : List Bool) : ℕ → Bool :=
  fun v => if v ∈ T then y.getD (T.idxOf v) false else false

/-- `F_T` as an explicit list: the patterns on `T` of induced cost at most `K`, in canonical
order. -/
def famList (I : GInst) (T : List ℕ) (K : ℕ) : List (List Bool) :=
  (allPatterns T.length).filter (fun y => decide (indCost I T.toFinset (listAsg T y) ≤ K))

/-- `s = ⌊m/u⌋` with `u = b^{1/ℓ}`, "computed by integer comparisons such as s^ℓ b ≤ m^ℓ" (p.13):
the largest `s ≤ m` with `s^ℓ b ≤ m^ℓ`. -/
def sSize (ℓ m b : ℕ) : ℕ :=
  Nat.findGreatest (fun s => s ^ ℓ * b ≤ m ^ ℓ) m

/-- Size of the drawn set: `0` when `m < ℓ` (no draw), else `s`. -/
def drawSize (ℓ m b : ℕ) : ℕ :=
  if m < ℓ then 0 else sSize ℓ m b

/-- The possible draws of the recovery procedure: all `s`-subsets of `[m]`, drawn uniformly. -/
def draws (ℓ m b : ℕ) : Finset (Finset ℕ) :=
  (Finset.range m).powersetCard (drawSize ℓ m b)

/-- Step (3) of the recovery procedure: the prediction of `x_i` (`i ∉ S`) from the seed `z`, using
`T = S ∪ {i}` (sorted), the family `F_T` of induced cost `≤ 16`, and the orientation
`orient (T, F_T)`. -/
def predict (orient : List ℕ × List (List Bool) → List (List Bool × ℕ)) (I : GInst)
    (S : Finset ℕ) (z : Fin I.n → Bool) (i : Fin I.n) : Bool :=
  let T := (insert (i : ℕ) S).sort (· ≤ ·)
  let z0 := Function.update (extA z) (i : ℕ) false
  let z1 := Function.update (extA z) (i : ℕ) true
  let in0 := decide (indCost I T.toFinset z0 ≤ 16)
  let in1 := decide (indCost I T.toFinset z1 ≤ 16)
  if in0 && in1 then decide ((T.map z0, T.idxOf (i : ℕ)) ∈ orient (T, famList I T 16))
  else in1

/-- **The recovery procedure of Lemma 3.3** (its output list, as a set of assignments), for the
drawn set `S` (the budget `b` enters only through the size of `S`, `draws`).

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §3.3, pp.12–13: "If m < ℓ there are no
constraints; output all 2^m < 2^ℓ assignments. Otherwise … draw a uniformly random s-set S.
(1) Enumerate the seeds: all assignments to S of induced cost at most 8. (2) For every i ∉ S,
compute F_{S∪{i}} and its canonical orientation O_{S∪{i}}. (3) For every seed z and every i ∉ S,
predict x_i from the two possible extensions (z, 0) and (z, 1) of z to S ∪ {i}: if exactly one lies
in F_{S∪{i}}, predict it; if both do, they are the endpoints of the edge of direction i, and we
predict its head under O_{S∪{i}}; if neither does, predict 0. (4) Output, for every seed z, the
candidate that agrees with z on S and with the predictions off S."

**Formalization Note.** The orientation rule `orient` is a parameter (Lemma 3.3 is stated for
every rule with the guarantee of Lemma 3.2, `GoodOrient`). Seeds are assignments vanishing off `S`;
`F_T` is passed to `orient` in canonical order (`famList`). The head of the edge `{(z,0),(z,1)}`
is `(z,1)` iff the edge is oriented away from `(z,0)`, so the prediction is `1` exactly then.
"Exactly one lies in F" predicts that one, "neither" predicts `0`: both are `in1` in `predict`. The
output is returned as a set (equal candidates from different seeds coincide). -/
def recoverSet (orient : List ℕ × List (List Bool) → List (List Bool × ℕ)) (ℓ : ℕ) (I : GInst)
    (S : Finset ℕ) : Finset (Fin I.n → Bool) :=
  if I.n < ℓ then Finset.univ else
    ((Finset.univ : Finset (Fin I.n → Bool)).filter
        (fun z => (∀ i : Fin I.n, (i : ℕ) ∉ S → z i = false) ∧ indCost I S (extA z) ≤ 8)).image
      (fun z => fun i => if (i : ℕ) ∈ S then z i else predict orient I S z i)

/-- `C_ℓ = 8(v_ℓ(16) + ℓ + 1)` (Lemma 3.3, (3), p.13). -/
def Cl (ℓ : ℕ) : ℕ := 8 * (vl ℓ 16 + ℓ + 1)

/-- The recovery radius `min{m, ⌈C_ℓ b^{1/ℓ}⌉}` (Lemma 3.3, (3), p.13). -/
noncomputable def recRadius (ℓ m b : ℕ) : ℕ :=
  min m ⌈(Cl ℓ : ℝ) * (b : ℝ) ^ ((1 : ℝ) / ℓ)⌉₊

end AcceptSubcube


