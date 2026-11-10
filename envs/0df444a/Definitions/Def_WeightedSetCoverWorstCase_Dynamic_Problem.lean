-- Prove2me | Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
-- name    : WeightedSetCoverWorstCase_Dynamic_Problem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:27:55.743707+00:00
-- url     : https://prove2.me/theorems/35601ab5-c111-4912-8476-c4912409acea
-- title:
--   Instances, adversarial updates, the aspect-ratio assumption, cost normalization, $L$, $\sigma$, set copies and recourse
-- statement:
--   A weighted set-cover instance is the published `DynSetCover.Instance`: base elements $U=\{0,\dots,n-1\}$ ($n=u$), input sets $S_0,\dots,S_{m-1}\subseteq U$ (an indexed family) with real costs $c(s)>0$, every base element lying in some input set. An **adversarial update** inserts a base element that is not live or deletes a live one (`Update.Legal`); `liveAfter` and `LegalSeq` follow a sequence of updates.
--
--   The standing assumption of footnote 1 ($C\le\mathrm{poly}(n)$) is the separate predicate `AspectBound inst d`: $c(s)\le\max(2,n)^d\,c(s')$ for all $s,s'$. §6.1 normalizes the costs into $[1/C,1]$: `ncost` $=c(s)/\max_{s'}c(s')$ and `Cint` $=\lceil\max c/\min c\rceil$. With $\varepsilon$ fixed, $L=\max\{1,\lceil\log_{1+\varepsilon}(Cn)\rceil\}$ (`Lpar`) and $\sigma=1000L^2/\varepsilon$ (`sigma`). `flog b x` $=\lfloor\log_b x\rfloor$.
--
--   A **set copy** (`Copy`) is an input set together with a coverage (a finite set of element versions) and a level. Solutions are multisets of copies (lists); `copiesCost` pays every copy, `copyRecourse` is the multiset symmetric difference of two lists of copies, and `copiesSets` is the deduplicated set family.
--
--   **Formalization Note.** `cmax`, `cmin` are $1$ when $m=0$ (then $u=0$ and nothing happens). $L$ at $n=0$ is $1$.
--
--   `Update`, `Update.apply` and `Update.Legal` are aliases of the published `DynSetCover_Updates` type and operations. The initial-live-set fold and legality predicate extend that interface to arbitrary initial sets; the normalization and copy definitions are specific to this paper.
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, §6.1, p. 21–22 (PDF 24–25); footnote 1, p. 1 (PDF 4)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_DynSetCover_Updates

namespace WeightedSetCoverWorstCase.Dynamic

/-!
# Fully dynamic weighted set cover: instances, updates, cost normalisation, parameters

Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), *Fully Dynamic Weighted Set Cover: Worst-Case
Recourse and Update Time*, STOC 2027 submission (supplied PDF sha256 28a86be4…), §6.1, p. 21–22
(PDF 24–25) and footnote 1, p. 1 (PDF 4).

* The instance is the published `DynSetCover.Instance`: base elements `Fin u` (so `n = u`), input
  sets `S : Fin m → Finset (Fin u)` (an indexed family), real costs `c0 s > 0`, and every base
  element lies in some input set. No rationality or aspect-ratio condition is bundled.
* An adversarial update inserts a base element that is not live or deletes a live one.
* The aspect-ratio assumption of footnote 1 (`C ≤ poly(n)`) is the separate predicate
  `AspectBound inst d`, stated only where the source uses it.
* §6.1 normalises costs into `[1/C, 1]` by a common factor; `ncost` divides by the largest cost,
  `Cint` is the least integer `C` with every normalised cost in `[1/C, 1]`, and
  `L = max{1, ⌈log_{1+ε}(C n)⌉}`, `σ = 1000 L² / ε` (the paper's `c_σ = 1000`).
-/

/-- The weighted set-cover instance: the published `DynSetCover.Instance`. -/
abbrev Instance := DynSetCover.Instance

/-- The published insertion/deletion update type, with the same base-element conventions. -/
abbrev Update := DynSetCover.Upd

namespace Update

/-- Alias of the published effect of an insertion/deletion on the live set. -/
abbrev apply {u : ℕ} (x : Update u) (A : Finset (Fin u)) := DynSetCover.Upd.apply x A

/-- Alias of the published legality predicate: insert an absent element or delete a live one. -/
abbrev Legal {u : ℕ} (x : Update u) (A : Finset (Fin u)) := DynSetCover.Upd.ValidAt x A

end Update

/-- The live base set after a finite sequence of updates applied to `A`. -/
def liveAfter {u : ℕ} (A : Finset (Fin u)) : List (Update u) → Finset (Fin u)
  | [] => A
  | x :: xs => liveAfter (x.apply A) xs

/-- A finite update sequence is legal from the live set `A` (every prefix legal). -/
def LegalSeq {u : ℕ} : Finset (Fin u) → List (Update u) → Prop
  | _, [] => True
  | A, x :: xs => x.Legal A ∧ LegalSeq (x.apply A) xs

/-- Footnote 1, p. 1: the ratio of maximum to minimum set cost is at most `poly(n)`, with the fixed
exponent `d`: `c(s) ≤ max(2,n)^d · c(s')` for all sets `s, s'`. -/
def AspectBound (inst : Instance) (d : ℕ) : Prop :=
  ∀ s s' : Fin inst.m, inst.c0 s ≤ ((max 2 inst.u : ℕ) : ℝ) ^ d * inst.c0 s'

/-- The largest set cost (`1` when there are no sets). -/
noncomputable def cmax (inst : Instance) : ℝ :=
  if h : 0 < inst.m then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ inst.c0 else 1

/-- The smallest set cost (`1` when there are no sets). -/
noncomputable def cmin (inst : Instance) : ℝ :=
  if h : 0 < inst.m then Finset.univ.inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ inst.c0 else 1

/-- §6.1 normalisation: the cost of `s` divided by the largest cost, so it lies in `(0, 1]`. -/
noncomputable def ncost (inst : Instance) (s : Fin inst.m) : ℝ := inst.c0 s / cmax inst

/-- `C`: the least integer with every normalised cost in `[1/C, 1]`, i.e. `⌈cmax / cmin⌉`. -/
noncomputable def Cint (inst : Instance) : ℕ := ⌈cmax inst / cmin inst⌉₊

/-- `⌊log_b x⌋` as an integer (`Real.logb`). Used only for `b = 1+ε > 1` and `x > 0`. -/
noncomputable def flog (b x : ℝ) : ℤ := ⌊Real.logb b x⌋

/-- `L = max{1, ⌈log_{1+ε}(C n)⌉}` (§6.1, p. 22), `n = u`. -/
noncomputable def Lpar (inst : Instance) (ε : ℝ) : ℕ :=
  max 1 (⌈Real.logb (1 + ε) ((Cint inst : ℝ) * (inst.u : ℝ))⌉).toNat

/-- The speed parameter `σ = c_σ L² / ε` with `c_σ = 1000` (§6.1, p. 22). -/
noncomputable def sigma (inst : Instance) (ε : ℝ) : ℝ := 1000 * (Lpar inst ε : ℝ) ^ 2 / ε

/-- A set copy of a (multiset) solution: the input set it copies, its coverage (a finite set of
element versions of type `V`) and its level. -/
structure Copy (m : ℕ) (V : Type) where
  set : Fin m
  cov : Finset V
  lvl : ℕ
  deriving DecidableEq

/-- The (original) cost of a multiset of set copies: every copy is paid. -/
noncomputable def copiesCost (inst : Instance) {V : Type} (C : List (Copy inst.m V)) : ℝ :=
  (C.map fun c => inst.c0 c.set).sum

/-- Copy-level recourse between two multisets of copies: `|A ∖ B| + |B ∖ A|` as multisets. -/
def copyRecourse {m : ℕ} {V : Type} [DecidableEq V] (A B : List (Copy m V)) : ℕ :=
  ((A : Multiset (Copy m V)) - (B : Multiset (Copy m V))).card +
    ((B : Multiset (Copy m V)) - (A : Multiset (Copy m V))).card

/-- The deduplicated set family of a multiset of copies (the paper's original output). -/
def copiesSets {m : ℕ} {V : Type} (C : List (Copy m V)) : Finset (Fin m) :=
  (C.map fun c => c.set).toFinset

end WeightedSetCoverWorstCase.Dynamic


