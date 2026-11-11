-- Prove2me | Definitions.Def_LZEndAccess_Main_StablePart
-- name    : LZEndAccess_Main_StablePart
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:33:59.158367+00:00
-- url     : https://prove2.me/theorems/81cd5a0b-5b1c-4584-a007-ac1df11c5811
-- title:
--   The stable jump $sJ$, bad phrases and suffixes, $T_{\mathrm{bad}}$, $\delta\ell$, $\delta r$, $(x)$-bad indices, $\Delta L$, $\Delta R$, $D_L$, $D_R$
-- statement:
--   For a phrase $P=S[a..b]$, $L(P)=S[a..a+\lfloor\tfrac23|P|\rfloor-1]$ is its prefix of length $\lfloor 2|P|/3\rfloor$ (empty when $|P|=1$).
--
--   - **Stable jump** (Definition 5.1): for $i$ in the phrase $P=S[a..b]$ with $i\in L(P)$, $sJ(i)=i-\delta\text{-}\mathrm{pre}(a,a+\lfloor\tfrac23|P|\rfloor-1)$; otherwise $sJ(i)$ is undefined. $sJ^x$ is the iterate.
--   - **Bad phrase, bad suffix** (Definition 5.6): with $b'$ the last index of $L(P)$, the bad phrase of $P$ is the phrase containing $sJ(b')$, and the bad suffix of $P$ is the set of $i\in L(P)$ with $sJ(i)$ in the bad phrase.
--   - $T_{\mathrm{bad}}$: the parent of $P$ is its bad phrase (phrases of length one are roots); $\pi_{\mathrm{bad}}^{(x)}(P)$ is the $x$-th ancestor and $\mathrm{depth}(P)$ its depth.
--   - $\delta\ell(P)=\ell_{b'}-\ell_{sJ(b')}$ and $\delta r(P)=r_{b'}-r_{sJ(b')}$.
--   - $i$ in phrase $P$ is **$(x)$-bad** if $sJ^y(i)$ is in the bad suffix of $\pi_{\mathrm{bad}}^{(y)}(P)$ for every $y\in[0..x]$.
--   - $\Delta L(P,B)=\sum_{x=0}^{B}\delta\ell(\pi_{\mathrm{bad}}^{(x)}(P))$ and $\Delta R(P,B)=\sum_{x=0}^{B}\delta r(\pi_{\mathrm{bad}}^{(x)}(P))$ for integers $B\ge -1$ ($\Delta L(P,-1)=\Delta R(P,-1)=0$).
--   - $D_L$ is the maximal integer $D$ with $\Delta L(P,D)\le L$, and $D_R$ the maximal integer with $\Delta R(P,D)\le R-k$.
--
--   **Formalization Note.** $\delta\ell$, $\delta r$ are undefined in the paper for a phrase with empty $L(P)$ (a root of $T_{\mathrm{bad}}$); they are $0$ here, and missing ancestors contribute $0$ to $\Delta L,\Delta R$. The maxima $D_L$, $D_R$ are taken over $D\in[-1..\mathrm{depth}(P)-1]$, the range on which every summand is defined in the paper.
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 23, Definition 5.1; p. 25, Definition 5.6; p. 26, T_bad, δℓ, δr, Definition 5.11; p. 29, ΔL, ΔR; p. 30, D_L, D_R

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd

set_option autoImplicit false

namespace LZEndAccess.Main

open Classical

/-!
# The stable part: `L(P)`, `sJ`, bad phrases and suffixes, `T_bad`, `δℓ`, `δr`, `ΔL`, `ΔR`,
`D_L`, `D_R`

Boneh, Gawrychowski, *Random Access to LZ-End: Faster and Deterministic*, arXiv:2607.14923
(sha256 3c96c6ff…), §5 pp. 23–30 (Definition 5.1, Definition 5.6, `T_bad` p. 26, `δℓ`, `δr`
p. 26, Definition 5.11, `ΔL`, `ΔR` p. 29, `D_L`, `D_R` p. 30).

**Formalization Note.**
* `L(P) = S[a..a + ⌊2|P|/3⌋ − 1]` (p. 23); `Lend Z t` is its last index and `InL Z t i` says
  `i ∈ L(P_t)`. `L(P)` is empty exactly when `|P| = 1`.
* `sJ(i) = i − δ-pre(a, a + ⌊2|P|/3⌋ − 1)` for `i ∈ L(P)`, `P` the phrase containing `i`;
  `none` (undefined) otherwise (Definition 5.1).
* `badPhrase Z t` is the phrase containing `sJ(b')`, `b'` the last index of `L(P_t)`
  (Definition 5.6); `none` when `L(P_t)` is empty (`|P_t| = 1`): such phrases are the roots of
  `T_bad`. `ancBad Z t x = π_bad^{(x)}(P_t)` (`none` above the root) and `depthBad Z t` is the
  depth of `P_t` in `T_bad`.
* `InBadSuffix Z t i`: `i ∈ L(P_t)` and `sJ(i)` lies in the bad phrase of `P_t`.
* `δℓ(P) = ℓ_{b'} − ℓ_{sJ(b')}`, `δr(P) = r_{b'} − r_{sJ(b')}` (p. 26), integers; they are
  undefined in the paper when `L(P)` is empty, and are `0` here (only roots of `T_bad`).
* `ΔL(P, B) = Σ_{x=0}^{B} δℓ(π_bad^{(x)}(P))` for an integer `B ≥ −1` (`ΔL(P, −1) = 0`), with
  `0` for missing ancestors; likewise `ΔR`.
* `D_L` (`D_R`) is the maximal integer `D` with `ΔL(D) ≤ L` (`ΔR(D) ≤ R − k`) (p. 30), the
  maximum taken over `D ∈ [−1..depth − 1]`, the range on which every summand `δℓ(π^{(x)})`,
  `x ≤ D`, is defined in the paper (`π^{(depth)}(P)` is a root).
-/

/-- The last index `a + ⌊2|P|/3⌋ − 1` of `L(P_t)`. -/
def Lend (Z : List Phrase) (t : ℕ) : ℕ := (ph Z t).a + 2 * (ph Z t).len / 3 - 1

/-- `i ∈ L(P_t) = S[a..a + ⌊2|P_t|/3⌋ − 1]`. -/
def InL (Z : List Phrase) (t i : ℕ) : Prop :=
  InPhrase Z t i ∧ i < (ph Z t).a + 2 * (ph Z t).len / 3

instance (Z : List Phrase) (t i : ℕ) : Decidable (InL Z t i) := by
  unfold InL; infer_instance

/-- The jumping rule `sJ` (Definition 5.1). -/
def sJ (Z : List Phrase) (i : ℕ) : Option ℕ :=
  if InL Z (phraseIdx Z i) i then
    some (i - deltaPre Z (ph Z (phraseIdx Z i)).a (Lend Z (phraseIdx Z i)))
  else none

/-- The iterate `sJ^x(i)`. -/
def sJiter (Z : List Phrase) : ℕ → ℕ → Option ℕ
  | 0, i => some i
  | x + 1, i => (sJiter Z x i).bind (sJ Z)

/-- The bad phrase of `P_t` (Definition 5.6): the phrase containing `sJ(b')`, `b'` the last
index of `L(P_t)`; `none` when `L(P_t)` is empty. -/
def badPhrase (Z : List Phrase) (t : ℕ) : Option ℕ :=
  if 0 < 2 * (ph Z t).len / 3 then
    some (phraseIdx Z (Lend Z t - deltaPre Z (ph Z t).a (Lend Z t)))
  else none

/-- `i` is in the bad suffix of `P_t` (Definition 5.6): `i ∈ L(P_t)` and `sJ(i)` is in the bad
phrase of `P_t`. -/
def InBadSuffix (Z : List Phrase) (t i : ℕ) : Prop :=
  InL Z t i ∧ ∃ Q j, badPhrase Z t = some Q ∧ sJ Z i = some j ∧ InPhrase Z Q j

/-- The `x`-th ancestor `π_bad^{(x)}(P_t)` in `T_bad` (p. 26). -/
def ancBad (Z : List Phrase) (t : ℕ) : ℕ → Option ℕ
  | 0 => some t
  | x + 1 => (ancBad Z t x).bind (badPhrase Z)

/-- The depth of `P_t` in `T_bad` (the largest `x` with `π_bad^{(x)}(P_t)` defined). -/
def depthBad (Z : List Phrase) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun x => (ancBad Z t x).isSome = true) Z.length

/-- `δℓ(P_t) = ℓ_{b'} − ℓ_{sJ(b')}` (p. 26); `0` when `L(P_t)` is empty. -/
def deltaL (Z : List Phrase) (t : ℕ) : ℤ :=
  if 0 < 2 * (ph Z t).len / 3 then
    match sJ Z (Lend Z t) with
    | some j => (lVal Z (Lend Z t) : ℤ) - lVal Z j
    | none => 0
  else 0

/-- `δr(P_t) = r_{b'} − r_{sJ(b')}` (p. 26); `0` when `L(P_t)` is empty. -/
def deltaR (Z : List Phrase) (t : ℕ) : ℤ :=
  if 0 < 2 * (ph Z t).len / 3 then
    match sJ Z (Lend Z t) with
    | some j => (rVal Z (Lend Z t) : ℤ) - rVal Z j
    | none => 0
  else 0

/-- `ΔL(P_t, B) = Σ_{x=0}^{B} δℓ(π_bad^{(x)}(P_t))` (p. 29); `ΔL(P_t, −1) = 0`. -/
def DeltaL (Z : List Phrase) (t : ℕ) (B : ℤ) : ℤ :=
  ∑ x ∈ Finset.range (B + 1).toNat, (match ancBad Z t x with
    | some Q => deltaL Z Q
    | none => 0)

/-- `ΔR(P_t, B) = Σ_{x=0}^{B} δr(π_bad^{(x)}(P_t))` (p. 29); `ΔR(P_t, −1) = 0`. -/
def DeltaR (Z : List Phrase) (t : ℕ) (B : ℤ) : ℤ :=
  ∑ x ∈ Finset.range (B + 1).toNat, (match ancBad Z t x with
    | some Q => deltaR Z Q
    | none => 0)

/-- `D_L`: the maximal integer `D ∈ [−1..depth − 1]` with `ΔL(P_t, D) ≤ L` (p. 30). -/
noncomputable def DL (Z : List Phrase) (t L : ℕ) : ℤ :=
  (Nat.findGreatest (fun m => DeltaL Z t ((m : ℤ) - 1) ≤ (L : ℤ)) (depthBad Z t) : ℤ) - 1

/-- `D_R`: the maximal integer `D ∈ [−1..depth − 1]` with `ΔR(P_t, D) ≤ R − k` (p. 30). -/
noncomputable def DR (Z : List Phrase) (t R : ℕ) (k : ℝ) : ℤ :=
  (Nat.findGreatest (fun m => (DeltaR Z t ((m : ℤ) - 1) : ℝ) ≤ (R : ℝ) - k) (depthBad Z t) : ℤ)
    - 1

/-- `i` is `(x)`-bad in `P_t` (Definition 5.11): for every `y ∈ [0..x]`, `sJ^y(i)` is in the bad
suffix of `π_bad^{(y)}(P_t)`. -/
def IsXBad (Z : List Phrase) (x t i : ℕ) : Prop :=
  ∀ y, y ≤ x → ∃ Q j, ancBad Z t y = some Q ∧ sJiter Z y i = some j ∧ InBadSuffix Z Q j

end LZEndAccess.Main


