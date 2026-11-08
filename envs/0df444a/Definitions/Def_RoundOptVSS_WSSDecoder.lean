-- Prove2me | Definitions.Def_RoundOptVSS_WSSDecoder
-- name    : RoundOptVSS_WSSDecoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:05:48.617234+00:00
-- url     : https://prove2.me/theorems/53beb64c-df7d-4801-b2aa-ac13512bd146
-- title:
--   The decoder $\mathrm{Dec}_{O}$ and the rejection test $\mathrm{Reject}_O$ of the key-uniform WSS (Protocol 7)
-- statement:
--   One instance $O$ of the WSS of §7.2 has $n$ parties, a dealer $D$ and row holders $I=[n]\setminus\{D\}$, party points $a_i\in\mathbb F$, and the packed-IC parameters of width $h$. Its labels are $W_{i,\ell}$ ($D\to P_i$, LATE), $S_{ij}$ ($D\to P_i$, EARLY), $Q_{ij}$ ($P_i\to D$, EARLY) and $R_{ij}$ ($P_i\to P_j$, LATE).
--
--   The **public sharing data** $\Gamma_O$ are: the round-two broadcasts $\mathrm{inv}_i$, $\phi_{ij}$, $a_{ij}$, $b_{ij}$, $a^D_{ij}$, $b^D_{ij}$; the checkpoint of every label; the replacement $x^{rep}_L$ of every label whose Verify output is a valid replacement ($c_L=1$); the repair set $U$ and repaired rows $u_i$; and the round-three EARLY candidates. A missing or malformed value reads as $\bot$, a missing or malformed flag as $1$. With $b_{ij}$ replaced by $\bot$ when $\phi_{ij}=1$, the trigger $\eta_i$ and the dispute flag $p_{ij}$ are given by (5), the required labels by (6), and a label is **activated** if it is required or its holder broadcast any candidate.
--
--   For a proposed assignment $k=(k_1,\dots,k_n)$ (each $k_w$ is `bad` or a key per EARLY label) the value $\mathrm{Early}(L;k)$ is the replacement if $c_L=1$; unavailable if $L$ is not activated; $\bot$ if no valid candidate was broadcast; otherwise the candidate's payload if at least $t+1$ of the $n$ votes (4) accept, and $\bot$ if not. A party's LATE value $\mathrm{Late}_h(L)$ uses its own stored key. With $s_{ij}=u_i(j)$ for $i\in U$ and $\mathrm{Early}(S_{ij};k)$ otherwise and $q_{ij}=\mathrm{Early}(Q_{ij};k)$, the **rejection test** $\mathrm{Reject}_O(\Gamma_O,k)=1$ iff one of the conditions (G1)–(G4) of Protocol 7 fails.
--
--   The **decoder** $\mathrm{Dec}_{O,h}(\sigma_h,k;\tau)$, with $\sigma_h=(\Gamma_O,\text{stored keys of }P_h)$ and $\tau$ the reconstruction openings (LATE candidates and the dealer's fallback), outputs $\bot$ if $\mathrm{Reject}_O(\Gamma_O,k)=1$; otherwise it retains rows by the tests of step 3 and outputs $\sum_{i\in J}L^J_i(0)f_i(0)$ for the first $t+1$ retained rows $J$, or the fallback (the zero vector if the fallback is missing or malformed) when fewer than $t+1$ rows are retained.
--
--   **Formalization Note** "A comparison with a ⊥ operand fails": an equality test with a ⊥ operand is false, hence a mismatch flag with a ⊥ operand is $1$. Rows are coordinatewise polynomials $\mathrm{Fin}\,h\to\mathbb E[X]$. The label index types contain all pairs of parties; only labels between distinct row holders are read.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), §7.2: label table (p.20), notation (p.20), (4) (p.21), Protocols 4–6 and (5), (6) (pp.21–22), Protocol 7 (p.23)

import Mathlib
import Definitions.Def_RoundOptVSS_PackedIC

open scoped Polynomial
open Polynomial Classical

namespace RoundOptVSS

/-!
# The decoder `Dec_O` of the key-uniform WSS (§7.2, Protocols 5–7)

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…), §7.2 (pp.20–23): the label
table (p.20), the notation paragraph (p.20), the vote (4) (p.21), the normalization of `b_ij`
and (5) (p.22), the required and activated labels (6) (p.22), and Protocol 7's decoder
`Dec_{O,h}(σ_h, k; τ)` with the rejection test `Reject_O(Γ_O, k)` = failure of (G1)–(G4) (p.23).

**Formalization Note.**
* The decoder is a pure function of the public sharing data `Γ_O` (`WSSTranscript`), the
  decoding party's private stored keys (normalized, one per label; only LATE labels are read),
  a proposed assignment `k` and an opening vector `τ`.
* `Γ_O` holds the broadcasts already read: flags (`inv_i`, `ϕ_ij`) as booleans (a missing or
  malformed flag is read as `1` = `true` when parsing), values `a_ij, b_ij, a^D_ij, b^D_ij` as
  `Option` (`none` = ⊥, missing or malformed), checkpoints as `Option (𝔽 × 𝔼[X])` (`none` =
  malformed), `rep L = some x` exactly when the Verify output of `L` is a valid replacement
  `fail(x)` (`c_L = 1`), the repair declaration `U` (`none` = malformed) and rows `u_i`
  (`none` = missing or malformed), and the round-three EARLY candidates (`none` = no broadcast,
  `some none` = a broadcast that does not parse, `some (some (x′, P))` = a parsed candidate).
* Parties are `Fin n`, the dealer is `D`, the row holders are `I = {i ≠ D}`; the label index
  types contain all pairs, and only the labels of the table (distinct row holders) are read.
* A value is a `LVal`: unavailable, ⊥ or finite `x ∈ 𝔼^h`. "A comparison with a ⊥ operand
  fails": an equality test with a ⊥ operand is false, so a mismatch test `[x ≠ y]` with a ⊥
  operand is true (`¬ eqF x y`).
* A proposed assignment gives each party `none` (= bad) or a vector with one key slot per EARLY
  label (the verification vector `κ_w`, three elements of `𝔼` per key).
* Rows are polynomials in `Y` with coefficients in `𝔼^h`, represented coordinatewise as
  `Fin h → 𝔼[X]`; "evaluation at i means evaluation at a_i".
-/

/-- The WSS parameters: the packed-IC parameters of width `h` plus the number of parties, the
dealer and the party points `a_i ∈ 𝔽`. -/
structure WSSParams (𝔽 : Type) extends ICParams 𝔽 where
  n : ℕ
  D : Fin n
  pt : Fin n → 𝔽

/-- The labels of the table (p.20): `W_{i,ℓ}` (D → P_i, coefficient `γ_{i,ℓ}`, LATE), `S_ij`
(D → P_i, `B(i, j)`, EARLY), `Q_ij` (P_i → D, pad `r_ij`, EARLY), `R_ij` (P_i → P_j, pad `r_ij`,
LATE). -/
inductive Label (n t : ℕ) where
  | W (i : Fin n) (l : Fin (t + 1))
  | S (i j : Fin n)
  | Q (i j : Fin n)
  | R (i j : Fin n)

/-- The EARLY labels `S_ij`, `Q_ij`. -/
inductive EarlyLabel (n : ℕ) where
  | S (i j : Fin n)
  | Q (i j : Fin n)

/-- An EARLY label as a label. -/
def EarlyLabel.toLabel {n t : ℕ} : EarlyLabel n → Label n t
  | .S i j => .S i j
  | .Q i j => .Q i j

/-- A label value: unavailable, ⊥, or finite. -/
inductive LVal (𝔼 : Type) (h : ℕ) where
  | unavailable : LVal 𝔼 h
  | bot : LVal 𝔼 h
  | fin : (Fin h → 𝔼) → LVal 𝔼 h

/-- The public sharing data `Γ_O` of one instance, as read by every party. -/
structure WSSTranscript (𝔽 𝔼 : Type) [Semiring 𝔼] (n t h : ℕ) where
  inv : Fin n → Bool
  phi : Fin n → Fin n → Bool
  a : Fin n → Fin n → Option (Fin h → 𝔼)
  b : Fin n → Fin n → Option (Fin h → 𝔼)
  aD : Fin n → Fin n → Option (Fin h → 𝔼)
  bD : Fin n → Fin n → Option (Fin h → 𝔼)
  cp : Label n t → Option (𝔽 × 𝔼[X])
  rep : Label n t → Option (Fin h → 𝔼)
  U : Option (Finset (Fin n))
  u : Fin n → Option (Fin h → 𝔼[X])
  cand : EarlyLabel n → Option (Option ((Fin h → 𝔼) × 𝔼[X]))

/-- The reconstruction openings `τ`: the LATE candidates (per label, `none` = missing or
malformed) and the dealer's fallback (`none` = missing or malformed). -/
structure WSSOpening (𝔼 : Type) [Semiring 𝔼] (n t h : ℕ) where
  late : Label n t → Option ((Fin h → 𝔼) × 𝔼[X])
  fallback : Option (Fin h → 𝔼)

/-- A proposed assignment: per party, `bad` (`none`) or a key in every EARLY slot. -/
abbrev Assignment (𝔼 : Type) (n : ℕ) := Fin n → Option (EarlyLabel n → ICKey 𝔼)

variable {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]

/-- Equality test in which a ⊥ operand fails. -/
def eqF {α : Type} (x y : Option α) : Prop := ∃ v, x = some v ∧ y = some v

/-- A row evaluated at a point. -/
noncomputable def rowEval {h : ℕ} (u : Fin h → 𝔼[X]) (a : 𝔽) : Fin h → 𝔼 :=
  fun c => (u c).eval (algebraMap 𝔽 𝔼 a)

/-- The coefficient `[Y^ℓ]` of a row. -/
noncomputable def rowCoeff {h : ℕ} (u : Fin h → 𝔼[X]) (l : ℕ) : Fin h → 𝔼 :=
  fun c => (u c).coeff l

/-- The row with coefficients `γ_0, …, γ_t`. -/
noncomputable def rowOfCoeffs {h t : ℕ} (γ : Fin (t + 1) → Fin h → 𝔼) : Fin h → 𝔼[X] :=
  fun c => ∑ l : Fin (t + 1), C (γ l c) * X ^ (l : ℕ)

section Decoder

variable (W : WSSParams 𝔽) (Γ : WSSTranscript 𝔽 𝔼 W.n W.t W.h)

/-- `i, j` are distinct row holders. -/
def RowPair (i j : Fin W.n) : Prop := i ≠ W.D ∧ j ≠ W.D ∧ i ≠ j

/-- The normalized comparison: `b_ij` is replaced by ⊥ when the received flag `ϕ_ij` is `1`. -/
def bn (i j : Fin W.n) : Option (Fin W.h → 𝔼) := if Γ.phi i j then none else Γ.b i j

/-- The row trigger `η_i` of (5). -/
def eta (i : Fin W.n) : Prop :=
  Γ.inv i = true ∨ ∃ j, j ≠ W.D ∧ j ≠ i ∧ ¬ eqF (Γ.a i j) (Γ.aD i j)

/-- The dispute flag `p_ij` of (5). -/
def disp (i j : Fin W.n) : Prop :=
  ¬ eqF (Γ.a i j) (bn W Γ j i) ∨ ¬ eqF (Γ.a j i) (bn W Γ i j) ∨
    ¬ eqF (Γ.a i j) (Γ.aD i j) ∨ ¬ eqF (bn W Γ i j) (Γ.bD i j)

/-- `c_L = 1`: the Verify output of `L` is a valid replacement. -/
def cflag (L : Label W.n W.t) : Prop := Γ.rep L ≠ none

/-- `i ∈ U` for the declared repair set. -/
def inU (i : Fin W.n) : Prop := ∃ U, Γ.U = some U ∧ i ∈ U

/-- The required labels (6). -/
def req : EarlyLabel W.n → Prop
  | .S i j => disp W Γ i j ∨ cflag W Γ (.R i j) ∨ ∃ k, k ≠ W.D ∧ k ≠ i ∧ cflag W Γ (.Q i k)
  | .Q i j => ¬ inU W Γ i ∧ inU W Γ j

/-- A label is activated if it is required or its holder broadcast any candidate. -/
def activated (L : EarlyLabel W.n) : Prop := req W Γ L ∨ Γ.cand L ≠ none

/-- `Early(L; k)` (Protocol 7, step 1): the replacement if `c_L = 1`; unavailable if not
activated; ⊥ if no valid candidate was broadcast; otherwise `x′` if at least `t + 1` of the `n`
votes (4) accept, else ⊥. -/
noncomputable def early (L : EarlyLabel W.n) (k : Assignment 𝔼 W.n) : LVal 𝔼 W.h :=
  match Γ.rep L.toLabel with
  | some xr => .fin xr
  | none =>
    if ¬ activated W Γ L then .unavailable else
    match Γ.cand L, Γ.cp L.toLabel with
    | some (some (x', P)), some cp =>
        if CandValid W.toICParams x' P then
          (if W.t + 1 ≤ (Finset.univ.filter fun w =>
              Check W.toICParams x' P cp ((k w).map fun v => v L)).card
            then .fin x' else .bot)
        else .bot
    | _, _ => .bot

/-- `Late_h(L)` (Protocol 7, step 1) under the decoding party's stored keys `key`: the
replacement if `c_L = 1`; ⊥ if no valid candidate was broadcast; otherwise `x′` if `Open`
accepts it under the stored key, else ⊥. -/
noncomputable def late (key : Label W.n W.t → ICKey 𝔼) (τ : WSSOpening 𝔼 W.n W.t W.h)
    (L : Label W.n W.t) : LVal 𝔼 W.h :=
  match Γ.rep L with
  | some xr => .fin xr
  | none =>
    match τ.late L, Γ.cp L with
    | some (x', P), some cp =>
        if Accepts W.toICParams x' P cp (some (key L)) then .fin x' else .bot
    | _, _ => .bot

/-- `s_ij`: `u_i(j)` if `i ∈ U`, else `Early(S_ij; k)`. -/
noncomputable def sVal (k : Assignment 𝔼 W.n) (i j : Fin W.n) : LVal 𝔼 W.h :=
  if inU W Γ i then
    (match Γ.u i with
     | some ui => .fin (rowEval ui (W.pt j))
     | none => .bot)
  else early W Γ (.S i j) k

/-- `q_ij = Early(Q_ij; k)`. -/
noncomputable def qVal (k : Assignment 𝔼 W.n) (i j : Fin W.n) : LVal 𝔼 W.h :=
  early W Γ (.Q i j) k

/-- (G1): `U ⊆ I`, `|U| ≤ t`, `U` contains every `i` with `η_i = 1` or a replacement on some
`S_ij` or `W_{i,ℓ}`, every `u_i` (`i ∈ U`) is present with degree at most `t` and agrees with
every replacement on its row. -/
def G1 : Prop :=
  ∃ U, Γ.U = some U ∧ (∀ i ∈ U, i ≠ W.D) ∧ U.card ≤ W.t ∧
    (∀ i, i ≠ W.D →
      (eta W Γ i ∨ (∃ j, RowPair W i j ∧ cflag W Γ (.S i j)) ∨ ∃ l, cflag W Γ (.W i l)) →
        i ∈ U) ∧
    ∀ i ∈ U, ∃ ui, Γ.u i = some ui ∧ (∀ c, (ui c).natDegree ≤ W.t) ∧
      (∀ j, RowPair W i j → ∀ xr, Γ.rep (.S i j) = some xr → rowEval ui (W.pt j) = xr) ∧
      (∀ l xr, Γ.rep (.W i l) = some xr → rowCoeff ui (l : ℕ) = xr)

/-- (G2): for every pair `{i, j}`, the finite values among `s_ij, s_ji` agree. -/
def G2 (k : Assignment 𝔼 W.n) : Prop :=
  ∀ i j, RowPair W i j → ∀ x y,
    sVal W Γ k i j = .fin x → sVal W Γ k j i = .fin y → x = y

/-- (G3): every activated `Q_ij` has finite `q_ij`. -/
def G3 (k : Assignment 𝔼 W.n) : Prop :=
  ∀ i j, RowPair W i j → activated W Γ (.Q i j) → ∃ x, qVal W Γ k i j = .fin x

/-- (G4): for every `i ∉ U`, `j ∈ U` with `c_{Q_ij} = 0`: `a^D_ij = b^D_ji = u_j(i) + q_ij`, all
operands finite. -/
def G4 (k : Assignment 𝔼 W.n) : Prop :=
  ∀ i j, RowPair W i j → ¬ inU W Γ i → inU W Γ j → Γ.rep (.Q i j) = none →
    ∃ v uj q, Γ.aD i j = some v ∧ Γ.bD j i = some v ∧ Γ.u j = some uj ∧
      qVal W Γ k i j = .fin q ∧ v = rowEval uj (W.pt i) + q

/-- `Reject_O(Γ_O, k) = 1`: one of (G1)–(G4) fails. -/
def Reject (k : Assignment 𝔼 W.n) : Prop :=
  ¬ (G1 W Γ ∧ G2 W Γ k ∧ G3 W Γ k ∧ G4 W Γ k)

variable (key : Label W.n W.t → ICKey 𝔼) (τ : WSSOpening 𝔼 W.n W.t W.h)
  (k : Assignment 𝔼 W.n)

/-- The coefficients `w_{i,0}, …, w_{i,t}` of an unrepaired row, if all are finite. -/
noncomputable def rowCoeffs (i : Fin W.n) : Option (Fin (W.t + 1) → Fin W.h → 𝔼) :=
  if hall : ∀ l, ∃ x, late W Γ key τ (.W i l) = .fin x then
    some fun l => Classical.choose (hall l)
  else none

/-- Row retention (Protocol 7, step 3) at the decoding party: a repaired row is retained; an
unrepaired row `i` is retained iff all `w_{i,ℓ}` are finite, `s_ij = f_i(j)` for every activated
`S_ij`, and for every `j ≠ i`: `j ∈ U ⇒ f_i(j) = u_j(i)`, `v_ij` finite `⇒ f_i(j) + v_ij = a_ij`,
and `c_{R_ji} = 0 ∧ ϕ_ij = 0 ⇒ v_ji` finite and `b_ij − v_ji = f_i(j)`. -/
def Retained (i : Fin W.n) : Prop :=
  i ≠ W.D ∧
    (inU W Γ i ∨
      ∃ γ, rowCoeffs W Γ key τ i = some γ ∧
        (∀ j, RowPair W i j → activated W Γ (.S i j) →
          sVal W Γ k i j = .fin (rowEval (rowOfCoeffs γ) (W.pt j))) ∧
        ∀ j, RowPair W i j →
          (inU W Γ j → ∃ uj, Γ.u j = some uj ∧
              rowEval (rowOfCoeffs γ) (W.pt j) = rowEval uj (W.pt i)) ∧
          (∀ v, late W Γ key τ (.R i j) = .fin v →
              ∃ aij, Γ.a i j = some aij ∧ rowEval (rowOfCoeffs γ) (W.pt j) + v = aij) ∧
          (Γ.rep (.R j i) = none → Γ.phi i j = false →
              ∃ v bij, late W Γ key τ (.R j i) = .fin v ∧ bn W Γ i j = some bij ∧
                bij - v = rowEval (rowOfCoeffs γ) (W.pt j)))

/-- `f_i(0)` for a row (`u_i(0)` for a repaired row, `w_{i,0}` otherwise). -/
noncomputable def rowAtZero (i : Fin W.n) : Fin W.h → 𝔼 :=
  if inU W Γ i then
    (match Γ.u i with
     | some ui => rowEval ui (0 : 𝔽)
     | none => 0)
  else
    (match rowCoeffs W Γ key τ i with
     | some γ => γ 0
     | none => 0)

/-- The retained rows in increasing index order. -/
noncomputable def retainedList : List (Fin W.n) :=
  (List.finRange W.n).filter fun i => decide (Retained W Γ key τ k i)

/-- `L^J_i(0)`, the Lagrange basis polynomial of `a_i` on `{a_j : j ∈ J}` at `0`. -/
noncomputable def lagrangeAtZero (J : Finset (Fin W.n)) (i : Fin W.n) : 𝔽 :=
  ∏ j ∈ J.erase i, ((0 : 𝔽) - W.pt j) / (W.pt i - W.pt j)

/-- Protocol 7, step 4: with `J` the first `t + 1` retained rows, `Σ_{i ∈ J} L^J_i(0) f_i(0)`;
with fewer retained rows, the dealer's fallback, or the zero vector if it is missing or
malformed. -/
noncomputable def decodeOutput : Fin W.h → 𝔼 :=
  if W.t + 1 ≤ (retainedList W Γ key τ k).length then
    let J := ((retainedList W Γ key τ k).take (W.t + 1)).toFinset
    ∑ i ∈ J, algebraMap 𝔽 𝔼 (lagrangeAtZero W J i) • rowAtZero W Γ key τ i
  else τ.fallback.getD 0

/-- `Dec_{O,h}(σ_h, k; τ)` (Protocol 7), with `σ_h = (Γ_O, key)`: ⊥ (`none`) if
`Reject_O(Γ_O, k)`, otherwise the output of steps 3–4. -/
noncomputable def Dec : Option (Fin W.h → 𝔼) :=
  if Reject W Γ k then none else some (decodeOutput W Γ key τ k)

end Decoder

end RoundOptVSS


