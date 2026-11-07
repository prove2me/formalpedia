-- Prove2me | Definitions.Def_DynConnWC_Events
-- name    : DynConnWC_Events
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:06.915323+00:00
-- url     : https://prove2.me/theorems/ca132b7c-26fb-4ee6-a938-7e9eabe3e76f
-- title:
--   Deficits along the run, the events $E_1$–$E_4$, the family $K_t$ and the parameters of §4.6
-- statement:
--   For a fixed update sequence, $G_t$ is the graph after update $t$, and $D_i(t)$ is $D(F_i)$ with respect to $G_t$ at the end of update $t$. $S_i$ counts the lower trees whose search returns a pair at the merge step of level $i$. With $h=128k$:
--
--   1. $E_1$: for every update and level, if $F_{i-1}\subseteq G$ at the merge step and $D(F_{i-1})\ge h$, then $S_i\ge D(F_{i-1})/64$.
--   2. $E_2$: for every update, level, lower tree searched by `UpdateWeights` and threshold, the fingerprint test is sound. That is, if $Z_j$ decodes to a pair and $P_j=\alpha^{Z_j}$, then the selected cut edges are that pair alone.
--   3. $K_t$: if $F_L$ is a forest of $G_t$ with $D_L(t)\le h$, the nonempty sets $\delta_{G_t}(S)$ over unions $S$ of trees of $F_L$; otherwise empty.
--   4. $E_3$: for every update and every cut in $K_t$, some final instance has a threshold selecting exactly one edge of the cut.
--   5. $E_4$: the fingerprint test is sound for every update, cut in $K_t$, final instance and threshold.
--
--   The **budget** (2)–(5) for $T_0$ and $\delta$ is
--   $$T_0Le^{-k/256}\le\delta/4,\quad 3T_0L(J+1)2^{J-w}\le\delta/4,\quad T_02^h(7/8)^r\le\delta/4,\quad T_02^hr(J+1)2^{J-w}\le\delta/4,$$
--   and §4.6 chooses $T_0=\lceil n^d\rceil$, $\delta=n^{-\beta}$, $k=2\lceil128\ln(4T_0L/\delta)\rceil$, $r=\lceil(h\ln2+\ln(4T_0/\delta))/\ln(8/7)\rceil$ and $w=J+\lceil\log_2(4T_0(J+1)(3L+2^hr)/\delta)\rceil$.
--
--   **Formalization Note** The fingerprint test has no endpoint condition, matching Appendix A.2 and p.22. `probR` is the probability under the uniform law on the random choices; the type is finite, so nothing is lost in `toReal`. The term $2^hr$ in $w$ is as printed on p.23; the text layer flattens it to `2hr`.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), §4, p.16 (PDF 17); §4.1, p.17 (PDF 18); Lemmas 15, 18, 21, pp.19–22; §4.6, p.23 (PDF 24)

import Mathlib
import Definitions.Def_DynConnWC_Algorithm

set_option autoImplicit false

namespace DynConnWC

/-! # Deficits along the run, the events E1–E4, and the parameters of §4.6

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), §4, p.16: "Let G_t be the graph after update t, and let D_i(t)
denote D(F_i) with respect to G_t at the end of update t; here t = 0 denotes the initial state";
§4.1, p.17: "Fix q = 127/128, L = 128⌈log₂ n⌉, h = 128k … let S_i be the number of lower trees
(trees of F_{i−1}) on which a search of C_i currently returns a pair"; Lemma 15, p.19 (E2);
Lemma 18, p.20 (E1); p.22: "If, at the end of update t, F_L is a forest of G_t with D_L(t) ≤ h,
then K_t is the set of nonempty edge sets δ_{G_t}(S) over all unions S of trees of F_L. Otherwise
K_t is empty"; Lemma 21, p.22 (E3, E4); §4.6, p.23: "Let δ = n^{−β} … k = 2⌈128 ln(4T0L/δ)⌉,
h = 128k, r = ⌈(h ln 2 + ln(4T0/δ))/ln(8/7)⌉, w = J + ⌈log₂(4T0(J + 1)(3L + 2^h r)/δ)⌉."

**Formalization Note.** Updates are numbered `t = 1, …, |σ|` and levels `i = 1, …, L`. "At the
merge step of level `i`" refers to the forests recorded by the algorithm after step 2(b) of level
`i` in update `t` (`recAt … t i`). `S_i` is computed from the current graph `G_t`, the instance
`C_i` and the lower forest at the merge step. In E2 and E4 the fingerprint test is
`FingerprintPasses` (decoding and `P_j = α^{Z_j}`), applied to the cut `δ_{G_t}(T)` of a searched
lower tree (E2) or to a cut in `K_t` (E4). `T0 = ⌈n^d⌉` is `⌈(n:ℝ)^d⌉₊`, `δ = n^{−β}` is real,
`ln` is `Real.log`, `log₂` is `Real.logb 2`, and every ceiling is `Nat.ceil`. `Budget` is the four
inequalities (2)–(5), which is all the analysis uses of the parameters; `Params46` says the parameters
are exactly §4.6's choices. `probR` is the probability of a set of random choices under the uniform
law (a probability measure on a finite type, so `toReal` loses nothing). -/

variable {n : ℕ}

/-- `q = 127/128`. -/
noncomputable def qpar : ℝ := 127 / 128

/-- `h = 128k`. -/
def hpar (S : AlgSetup n) : ℕ := 128 * S.k

/-- The probability of a set of random choices under `randLaw`, as a real number. -/
noncomputable def probR (S : AlgSetup n) (A : Set (RandChoices S)) : ℝ :=
  ((randLaw S).toOuterMeasure A).toReal

/-- The graph `G_t` after the first `t` updates of `σ`. -/
noncomputable def Gt (σ : List (PunctSketch.Update n)) (t : ℕ) : SimpleGraph (Fin n) :=
  PunctSketch.streamGraph (σ.take t)

/-- `D_i(t)`: the deficit of `F_i` with respect to `G_t` at the end of update `t`. -/
noncomputable def Dlev (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n))
    (i t : ℕ) : ℤ :=
  deficit (Gt σ t) ((stateAt S R σ t).F i)

open Classical in
/-- The number of trees of `lower` on which the search of the instance `co` in `G` returns a
pair. -/
noncomputable def Scount (S : AlgSetup n) (co : Coins S.w S.k) (G : SimpleGraph (Fin n))
    (lower : Finset (Sym2 (Fin n))) : ℕ :=
  ((trees lower).filter (fun P => (search S.mode S.enc co G P).isSome)).card

/-- `S_i` at the merge step of level `i` in update `t`. -/
noncomputable def Smerge (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n))
    (t i : ℕ) : ℕ :=
  Scount S (R.lev i) (Gt σ t) (recAt S R σ t i).lowerAtMerge

/-- **E1** (Lemma 18): for every update `t` and level `i`, if `F_{i−1} ⊆ G` at the merge step of
level `i` and `D(F_{i−1}) ≥ h`, then `S_i ≥ D(F_{i−1})/64` at that merge step. -/
def E1 (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ σ.length → ∀ i, 1 ≤ i → i ≤ Lpar n →
    SubG (recAt S R σ t i).lowerAtMerge (Gt σ t) →
    (hpar S : ℤ) ≤ deficit (Gt σ t) (recAt S R σ t i).lowerAtMerge →
    (deficit (Gt σ t) (recAt S R σ t i).lowerAtMerge : ℝ) / 64 ≤ Smerge S R σ t i

/-- **E2** (Lemma 15): for every update, every level `i`, every lower tree searched by
`UpdateWeights_i` and every threshold `j ∈ {0, …, J}`, the fingerprint test of `C_i` at `j` is
sound. -/
def E2 (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ σ.length → ∀ i, 1 ≤ i → i ≤ Lpar n →
    ∀ T ∈ (recAt S R σ t i).searched, ∀ j, j ≤ Jbits n →
      FingerprintSound S.enc (R.lev i) (cutset (Gt σ t) T) j

open Classical in
/-- `K_t` (p.22): if at the end of update `t` the forest `F_L` is a forest of `G_t` with
`D_L(t) ≤ h`, the nonempty cutsets `δ_{G_t}(S)` of the unions `S` of trees of `F_L`; otherwise
empty. -/
noncomputable def Kt (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n))
    (t : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  if IsForestSet ((stateAt S R σ t).F (Lpar n)) ∧ SubG ((stateAt S R σ t).F (Lpar n)) (Gt σ t) ∧ Dlev S R σ (Lpar n) t ≤ hpar S then
    ((unionsOfTrees ((stateAt S R σ t).F (Lpar n))).image (cutset (Gt σ t))).filter
      (fun C => C.Nonempty)
  else ∅

/-- **E3** (Lemma 21): for every update `t` and every cut in `K_t`, some final cutset instance has
a threshold that selects exactly one edge of the cut. -/
def E3 (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ σ.length → ∀ C ∈ Kt S R σ t,
    ∃ j < S.r, ∃ thr ≤ Jbits n, (selCut S.enc (R.fin j).1 C thr).card = 1

/-- **E4** (Lemma 21): the fingerprint test is sound for every update `t`, every cut in `K_t`,
every final cutset instance and every threshold. -/
def E4 (S : AlgSetup n) (R : RandChoices S) (σ : List (PunctSketch.Update n)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ σ.length → ∀ C ∈ Kt S R σ t, ∀ j < S.r, ∀ thr, thr ≤ Jbits n →
    FingerprintSound S.enc (R.fin j) C thr

/-- `T0 = ⌈n^d⌉`. -/
noncomputable def T0par (n : ℕ) (d : ℝ) : ℕ := ⌈(n : ℝ) ^ d⌉₊

/-- `δ = n^{−β}`. -/
noncomputable def deltaPar (n : ℕ) (β : ℝ) : ℝ := (n : ℝ) ^ (-β)

/-- §4.6: `k = 2⌈128 ln(4T0L/δ)⌉`. -/
noncomputable def k46 (n : ℕ) (d β : ℝ) : ℕ :=
  2 * ⌈128 * Real.log (4 * T0par n d * Lpar n / deltaPar n β)⌉₊

/-- §4.6: `h = 128k`. -/
noncomputable def h46 (n : ℕ) (d β : ℝ) : ℕ := 128 * k46 n d β

/-- §4.6: `r = ⌈(h ln 2 + ln(4T0/δ))/ln(8/7)⌉`. -/
noncomputable def r46 (n : ℕ) (d β : ℝ) : ℕ :=
  ⌈((h46 n d β : ℝ) * Real.log 2 + Real.log (4 * T0par n d / deltaPar n β)) /
      Real.log (8 / 7)⌉₊

/-- §4.6: `w = J + ⌈log₂(4T0(J + 1)(3L + 2^h r)/δ)⌉`. -/
noncomputable def w46 (n : ℕ) (d β : ℝ) : ℕ :=
  Jbits n + ⌈Real.logb 2 (4 * T0par n d * (Jbits n + 1) *
      (3 * Lpar n + 2 ^ h46 n d β * r46 n d β) / deltaPar n β)⌉₊

/-- The parameters of the setup are exactly the choices of §4.6 for `d` and `β`. -/
def Params46 (S : AlgSetup n) (d β : ℝ) : Prop :=
  S.k = k46 n d β ∧ S.w = w46 n d β ∧ S.r = r46 n d β

/-- The error budget (2)–(5) of §4.6, p.23, for an update bound `T0` and a failure probability `δ`. -/
def Budget (S : AlgSetup n) (T0 : ℕ) (δ : ℝ) : Prop :=
  (T0 : ℝ) * Lpar n * Real.exp (-(S.k : ℝ) / 256) ≤ δ / 4 ∧
  3 * (T0 : ℝ) * Lpar n * (Jbits n + 1) * (2 : ℝ) ^ ((Jbits n : ℤ) - S.w) ≤ δ / 4 ∧
  (T0 : ℝ) * 2 ^ hpar S * (7 / 8 : ℝ) ^ S.r ≤ δ / 4 ∧
  (T0 : ℝ) * 2 ^ hpar S * S.r * (Jbits n + 1) * (2 : ℝ) ^ ((Jbits n : ℤ) - S.w) ≤ δ / 4

end DynConnWC


