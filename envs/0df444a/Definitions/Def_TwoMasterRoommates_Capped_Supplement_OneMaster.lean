-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Supplement_OneMaster
-- name    : TwoMasterRoommates_Capped_Supplement_OneMaster
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:32:36.525721+00:00
-- url     : https://prove2.me/theorems/2558d323-0b75-434b-a972-115cd78d999d
-- title:
--   One weak master plus outliers: instances, weak stability, input code, and the §C.1 menus and buckets
-- statement:
--   An instance on $N$ agents $V=\{0,\dots,N-1\}$ splits $V$ into followers $F$ and outliers $S$, and supplies a weak order $\rho$ on all of $V$ (integer ranks, smaller is better, equal ranks form a tier) and, for each outlier $o$, an arbitrary complete weak row $r_o$. A follower $f$ ranks every candidate $x$ by $r_f(x)=\rho(x)$. A pair of distinct agents $u,v$ blocks a perfect matching $M$ when $r_u(v)<r_u(M(u))$ and $r_v(u)<r_v(M(v))$; a weakly stable perfect matching is a perfect matching (an involution without fixed points) with no blocking pair. Put $s=|S|$. The input code lists $N$, the outlier flags, $\rho$, the outlier rows and the rational weights on all pairs. A correct output is `0` when no weakly stable perfect matching exists, or `1` followed by the code of a weakly stable perfect matching of maximum total weight.
--
--   For an outlier $o$ let $F_o^+=\{f\in F:\rho(f)>\rho(o)\}$, let $k_o=\min\{s+2,|F_o^+|\}$, and let $\theta_o$ be the $k_o$-th smallest element of the multiset $\{r_o(f):f\in F_o^+\}$, counted with multiplicity. Put $T_o=\emptyset$ if $F_o^+=\emptyset$ and otherwise
--
--   $$T_o=\{r_o(f): f\in F_o^+,\ r_o(f)\le\theta_o\}.$$
--
--   The critical set is $C_o=\{r_o(o'):o'\in S\setminus\{o\}\}\cup T_o$. Its cells are the singletons $\{c\}$, $c\in C_o$, and the open intervals between consecutive critical values, including the two unbounded end intervals (the whole line when $C_o=\emptyset$). The local qualities are $\Lambda_o=\{r_o(f):f\in F,\ \rho(f)\le\rho(o)\}$. A local bucket $B_o$ is a nonempty set $X\cap\Lambda_o$, $X$ a cell, further intersected with $(-\infty,\theta_o]$ when $|F_o^+|\ge s+2$.
--
--   These objects are the model of Theorem C.1 and the menus and buckets of §C.1.
--
--   **Formalization Note** The order statistic returns $0$ outside $1\le k\le$ the multiset's size; it is only used inside that range. Follower rows and self entries are stored but never read. A cell's ends are critical values or $\pm\infty$ and it contains no critical value; when those ends are out of order the cell is empty and yields no bucket.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 18 (PDF p. 19), Theorem C.1 and the paragraph after it; p. 19 (PDF p. 20), §C.1 (definitions of $F_o^+$, $\theta_o$, $T_o$, $C_o$, cells, local qualities and buckets)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Instance
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_Common

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

open TwoMasterRoommates.Capped

/-- One supplied weak master plus outliers (Appendix C). `isOut v = true` puts `v` in the outlier
set `S`, otherwise `v` is a follower in `F`. `ρ` is the supplied weak order on all of `V`
(smaller is better, equal values form a tier). `row o` is the arbitrary complete weak row of an
outlier `o`; the rows of followers and the self entries are never read. -/
structure OneMasterInstance (N : ℕ) where
  isOut : Fin N → Bool
  ρ : Fin N → ℤ
  row : Fin N → Fin N → ℤ

namespace OneMasterInstance

variable {N : ℕ} (I : OneMasterInstance N)

/-- The rank `r_v(x)` of candidate `x` for observer `v`: the outlier's own row, or the master `ρ`
for a follower (whose own identity is never an available partner). -/
def r (v x : Fin N) : ℤ := if I.isOut v then I.row v x else I.ρ x

/-- `{u, v}` blocks `M`: distinct agents, each strictly preferring the other to its partner,
on the original weak rows (equation (1)). -/
def Blocks (M : Fin N → Fin N) (u v : Fin N) : Prop :=
  u ≠ v ∧ I.r u v < I.r u (M u) ∧ I.r v u < I.r v (M v)

/-- A weakly stable perfect matching. -/
def IsStable (M : Fin N → Fin N) : Prop :=
  IsPerfectMatching M ∧ ∀ u v, ¬ I.Blocks M u v

/-- The number `s = |S|` of outliers. -/
def s : ℕ := (Finset.univ.filter fun v => I.isOut v = true).card

/-- Binary input code: `N`, the outlier flags, `ρ`, the rows of the outliers, and the rational
weights on all unordered pairs `{i, j}`, `i < j`. -/
def enc (w : Sym2 (Fin N) → ℚ) : List Bool :=
  encNat N ++ List.ofFn I.isOut ++ (List.ofFn I.ρ).flatMap encInt ++
    (List.finRange N).flatMap (fun v =>
      if I.isOut v then (List.ofFn (I.row v)).flatMap encInt else []) ++
    encWeights encRat w

/-- A correct output of Theorem C.1: `[false]` when no weakly stable perfect matching exists, or
`true` followed by the code of a maximum-weight weakly stable perfect matching. -/
def CorrectC1 (w : Sym2 (Fin N) → ℚ) (y : List Bool) : Prop :=
  (y = [false] ∧ ¬ ∃ M, I.IsStable M) ∨
  ∃ M, y = true :: encM M ∧ I.IsStable M ∧
    ∀ M', I.IsStable M' → edgeSum w M' ≤ edgeSum w M

/-! ### The quantities of §C.1 -/

/-- `F_o^+ = {f ∈ F : ρ(f) > ρ(o)}`. -/
def Fplus (o : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun f => I.isOut f = false ∧ I.ρ o < I.ρ f

/-- The multiset `{r_o(f) : f ∈ F_o^+}` (with multiplicity). -/
def suffixRanks (o : Fin N) : Multiset ℤ := (I.Fplus o).val.map (I.row o)

/-- The `k`-th smallest element (`k ≥ 1`) of a multiset of integers, counted with multiplicity.
(Value `0` outside `1 ≤ k ≤ card`; it is only used inside that range.) -/
def kthSmallest (m : Multiset ℤ) (k : ℕ) : ℤ := (m.sort (· ≤ ·)).getD (k - 1) 0

/-- `θ_o`: the `k_o`-th smallest element of the multiset `{r_o(f) : f ∈ F_o^+}`, where
`k_o = min(s + 2, |F_o^+|)`. When `|F_o^+| ≥ s + 2` this is the `(s+2)`-nd smallest element. -/
def theta (o : Fin N) : ℤ :=
  kthSmallest (I.suffixRanks o) (min (I.s + 2) (I.Fplus o).card)

/-- `T_o`: empty if `F_o^+ = ∅`, otherwise `{r_o(f) : f ∈ F_o^+, r_o(f) ≤ θ_o}`. -/
def Tset (o : Fin N) : Finset ℤ :=
  if I.Fplus o = ∅ then ∅ else
    ((I.Fplus o).filter fun f => I.row o f ≤ I.theta o).image (I.row o)

/-- The critical set `C_o = {r_o(o') : o' ∈ S ∖ {o}} ∪ T_o`. -/
def critical (o : Fin N) : Finset ℤ :=
  ((Finset.univ.filter fun o' => I.isOut o' = true ∧ o' ≠ o).image (I.row o)) ∪ I.Tset o

/-- The attained local-follower qualities `{r_o(f) : f ∈ F, ρ(f) ≤ ρ(o)}`. -/
def localQualities (o : Fin N) : Set ℤ :=
  {q | ∃ f, I.isOut f = false ∧ I.ρ f ≤ I.ρ o ∧ I.row o f = q}

end OneMasterInstance

/-- `x` lies in the open interval with lower end `lo` and upper end `hi`
(`none` = unbounded on that side). -/
def InOpen (lo hi : Option ℤ) (x : ℤ) : Prop :=
  (∀ l, lo = some l → l < x) ∧ (∀ h, hi = some h → x < h)

/-- The cells of the rank line cut by a finite critical set `C`: each singleton `{c}`, `c ∈ C`,
and each open interval between consecutive critical values, including the two unbounded end
intervals (the whole line when `C = ∅`). An interval's ends are critical values or `±∞`, and
it contains no critical value. -/
def IsCell (C : Finset ℤ) (X : Set ℤ) : Prop :=
  (∃ c ∈ C, X = {c}) ∨
  ∃ lo hi : Option ℤ, (∀ l, lo = some l → l ∈ C) ∧ (∀ h, hi = some h → h ∈ C) ∧
    (∀ c ∈ C, ¬ InOpen lo hi c) ∧ X = {x | InOpen lo hi x}

namespace OneMasterInstance

variable {N : ℕ} (I : OneMasterInstance N)

/-- A local bucket `B_o`: a nonempty set `cell ∩ Λ_o`, further intersected with `(-∞, θ_o]` when
`|F_o^+| ≥ s + 2`. -/
def IsLocalBucket (o : Fin N) (B : Set ℤ) : Prop :=
  B.Nonempty ∧ ∃ X, IsCell (I.critical o) X ∧
    B = X ∩ I.localQualities o ∩
      (if I.s + 2 ≤ (I.Fplus o).card then Set.Iic (I.theta o) else Set.univ)

end OneMasterInstance

end TwoMasterRoommates.Capped.Supplement


