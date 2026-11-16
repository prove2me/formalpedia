-- Prove2me | Definitions.Def_PrivOptTest_Supplement_algo3
-- name    : PrivOptTest_Supplement_algo3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:34:31.78035+00:00
-- url     : https://prove2.me/theorems/e6fa5e67-d356-4512-8550-a55420b96ded
-- title:
--   Algorithm 3 $\mathcal A_{\mathrm{val-hs}}$ (private elimination over the dual space) as a two-party protocol
-- statement:
--   Algorithm 3 is run with public inputs: a finite dual discretization $\mathcal W$ and a container map $\mathcal C$ (as in Lemmas 4.3 and 4.5), a resolution $t$ and a privacy parameter $\varepsilon$. Alice holds $S_A\in\mathcal X^n$ and Bob $S_B\in\mathcal X^n$. Set
--   $$Q=\lceil\log_{4/3}|\mathcal W|\rceil+2,\qquad k=\Big\lfloor\frac{t-1}{2(d+1)}\Big\rfloor,\qquad \varepsilon_0=\varepsilon/Q,$$
--   and $\mathcal W_0=\mathcal W$. With the local errors $f_A(w)=\#\{x\in S_A:h_w(x)\ne-1\}$ and $f_B(w)=\#\{x\in S_B:h_w(x)\ne+1\}$, in round $r=0,\dots,Q-1$:
--
--   1. the public menu is $\mathcal R_r=\{C\in\mathcal C(\mathcal W_r):|C|\le\tfrac34|\mathcal W_r|\}\cup\{\bot\}$;
--   2. the cost of party $P$ is $q_{P,\mathcal W_r}(C;S_P)=\max_{h\in\mathcal W_r\setminus C}(k+1-f_P(h))_+$ for $C\ne\bot$ (the maximum of the empty set is $0$) and $q(\bot)=k/2$;
--   3. Alice releases $C_{A,r}$, sampled from the exponential mechanism on $\mathcal R_r$ with weights $\exp(-\varepsilon_0 q_{A,\mathcal W_r}(\cdot;S_A)/2)$; then Bob releases $C_{B,r}$ in the same way with $q_B$;
--   4. if $C_{A,r}=C_{B,r}=\bot$ the output is Match; otherwise $\mathcal W_{r+1}=C_{A,r}$ if $C_{A,r}\ne\bot$, else $C_{B,r}$.
--
--   After round $Q-1$ the output is Far if $\mathcal W_Q=\emptyset$ and Match otherwise.
--
--   This is the protocol of Theorem 4.7, the paper's resolution bound for halfspaces that does not depend on $n$.
--
--   **Formalization Note** Each party's private coins are $Q$ independent uniforms on $[0,1)$, one per round; the release is drawn from that round's coin by inverse CDF, which gives the exponential-mechanism law of Lemma B.4 with sensitivity $\Delta=1$. Line 3's $\alpha$ is used only in the analysis, never by the algorithm, so it is not computed. Released containers are written as subsets of $\mathcal W$.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Algorithm 3, p.30; Lemma B.4, p.40; local errors, p.28

import Mathlib
import Definitions.Def_PrivOptTest_Protocol
import Definitions.Def_PrivOptTest_Supplement_HhsOn

open MeasureTheory

namespace PrivOptTest

namespace Supplement

/-- Inverse-CDF selection from a finite list with nonnegative weights `w`: walk down the list,
subtracting weights from `v`, and return the first element whose weight exceeds what is left of `v`;
`dflt` if the list is exhausted. -/
noncomputable def pickAux {α : Type} (w : α → ℝ) (dflt : α) : List α → ℝ → α
  | [], _ => dflt
  | a :: l, v => if v < w a then a else pickAux w dflt l (v - w a)

/-- **A sample of the exponential mechanism from one uniform coin** (Lemma B.4, p.40). On the menu
`R` with positive weights `w`, a coin `u` uniform on `[0, 1)` returns `r ∈ R` with probability
`w(r) / Σ_{r' ∈ R} w(r')`. -/
noncomputable def emPick {α : Type} (R : Finset α) (w : α → ℝ) (dflt : α) (u : ℝ) : α :=
  pickAux w dflt R.toList (u * ∑ r ∈ R, w r)

/-- A history as a total function, with `dflt` beyond its length. -/
def histAt {M : Type} {r : ℕ} (dflt : M) (h : Fin r → M) (j : ℕ) : M :=
  if hj : j < r then h ⟨j, hj⟩ else dflt

variable {d : ℕ}

/-- The local errors of the halfspace `w` (p.28): `f_A(w) = #{x ∈ S_A : h_w(x) ≠ −1}` on Alice's data
and `f_B(w) = #{x ∈ S_B : h_w(x) ≠ +1}` on Bob's, records counted with multiplicity. `alice = true`
gives `f_A`. -/
noncomputable def localErr {X : Finset (EuclideanSpace ℝ (Fin d))} {n : ℕ} (alice : Bool)
    (S : Fin n → ↥X) (w : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (Finset.univ.filter fun i => hs w (S i : EuclideanSpace ℝ (Fin d)) ≠ !alice).card

/-- A message of Algorithm 3: `none` is `⊥`, `some C` a released container `C ⊆ W`. -/
abbrev Algo3Msg (W : Finset (EuclideanSpace ℝ (Fin d))) : Type := Option (Finset ↥W)

/-- The active sets `W_r` (lines 1 and 13–16 of Algorithm 3, p.30), read from the public messages:
round `2r` is Alice's release `C_{A,r}`, round `2r + 1` Bob's `C_{B,r}`. `W_0 = W`;
`W_{r+1} = C_{A,r}` if `C_{A,r} ≠ ⊥`, else `C_{B,r}` if `C_{B,r} ≠ ⊥` (if both are `⊥` the run has
already stopped and the value is not used). -/
def activeSet {W : Finset (EuclideanSpace ℝ (Fin d))} (m : ℕ → Algo3Msg W) : ℕ → Finset ↥W
  | 0 => Finset.univ
  | r + 1 =>
    match m (2 * r), m (2 * r + 1) with
    | some C, _ => C
    | none, some C => C
    | none, none => activeSet m r

/-- The public menu `R_r` of line 7 (p.30): `{C ∈ C(W_r, 1/4) : |C| ≤ (3/4)|W_r|} ∪ {⊥}`, with the
containers `C ⊆ W_r ⊆ W` written as subsets of `W`. -/
noncomputable def menu {W : Finset (EuclideanSpace ℝ (Fin d))}
    (cont : Finset (EuclideanSpace ℝ (Fin d)) → Finset (Finset (EuclideanSpace ℝ (Fin d))))
    (V : Finset ↥W) : Finset (Algo3Msg W) :=
  insert none
    (((cont (V.map (Function.Embedding.subtype _))).filter
        fun C => (C.card : ℝ) ≤ 3 / 4 * (V.card : ℝ)).image
      fun C => some (W.attach.filter fun w => w.1 ∈ C))

/-- The cost of line 8 (p.30): `q_{P,W_r}(C; S_P) = max_{h ∈ W_r \ C} (k + 1 − f_P(h))₊` for `C ≠ ⊥`
(the maximum over the empty set is `0`), and `q(⊥) = k/2`. The truncated subtraction of `ℕ` is the
positive part. -/
noncomputable def cost {W : Finset (EuclideanSpace ℝ (Fin d))} (f : EuclideanSpace ℝ (Fin d) → ℕ)
    (k : ℕ) (V : Finset ↥W) : Algo3Msg W → ℝ
  | none => (k : ℝ) / 2
  | some C => (((V \ C).sup fun h => k + 1 - f h.1 : ℕ) : ℝ)

/-- The number of rounds `Q = ⌈log_{4/3} |W|⌉ + 2` (line 2). -/
noncomputable def rounds (W : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ⌈Real.logb (4 / 3) (W.card : ℝ)⌉₊ + 2

/-- The release of party `P` in round `r` (lines 9–10): with `k = ⌊(t − 1)/(2(d + 1))⌋` (line 4) and
`ε₀ = ε/Q` (line 5), a sample of the exponential mechanism on the menu `R_r` with weights
`exp(−ε₀ q_{P,W_r}(·; S_P)/2)` (Lemma B.4 with sensitivity `Δ = 1`), drawn from the party's coin `u`. -/
noncomputable def release {X : Finset (EuclideanSpace ℝ (Fin d))} {n : ℕ} (t : ℕ) (ε : ℝ)
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (cont : Finset (EuclideanSpace ℝ (Fin d)) → Finset (Finset (EuclideanSpace ℝ (Fin d))))
    (alice : Bool) (S : Fin n → ↥X) (u : ℝ) (V : Finset ↥W) : Algo3Msg W :=
  let k := (t - 1) / (2 * (d + 1))
  let ε₀ := ε / (rounds W : ℝ)
  emPick (menu cont V) (fun C => Real.exp (-(ε₀ * cost (localErr alice S) k V C) / 2)) none u

/-- The public stopping rule of Algorithm 3 (lines 11–12 and 17). After Bob's release in round `r`
(that is, before message `2r + 2`): Match if `C_{A,r} = C_{B,r} = ⊥`; otherwise, after the last round
`r = Q − 1`, Far if `W_Q = ∅` and Match if not. -/
noncomputable def algo3Stop {W : Finset (EuclideanSpace ℝ (Fin d))} (Q : ℕ) (r : ℕ)
    (m : ℕ → Algo3Msg W) : Outcome ⊕ Unit :=
  if r ≠ 0 ∧ r % 2 = 0 then
    if m (r - 2) = none ∧ m (r - 1) = none then Sum.inl Outcome.matched
    else if Q ≤ r / 2 then
      Sum.inl (if activeSet m (r / 2) = ∅ then Outcome.far else Outcome.matched)
    else Sum.inr ()
  else Sum.inr ()

/-- The coin of round `r`, as a total function. -/
def coinAt {Q : ℕ} (ω : Fin Q → ℝ) (r : ℕ) : ℝ := if h : r < Q then ω ⟨r, h⟩ else 0

/-- **Algorithm 3, `A_val−hs` (Data Valuation for Half Spaces), p.30**, as a two-party protocol with
public inputs `W` (the finite dual discretization `W_disc` of Lemma 4.3) and `cont` (the container
family `C(·, 1/4)` of Lemma 4.5). Alice holds `S_A ∈ Xⁿ`, Bob `S_B ∈ Xⁿ`. For `r = 0, …, Q − 1`, Alice
releases `C_{A,r} ∼ EM(q_{A,W_r}, R_r, S_A, ε₀)` (message `2r`), then Bob releases
`C_{B,r} ∼ EM(q_{B,W_r}, R_r, S_B, ε₀)` (message `2r + 1`); both `⊥` returns Match; otherwise
`W_{r+1}` is `C_{A,r}` if it is not `⊥`, else `C_{B,r}`. After round `Q − 1`: Far if `W_Q = ∅`, else
Match.

**Formalization Note.** Each party's private coins are `Q` independent uniform samples on `[0, 1)`, one
per round, and its release is the exponential-mechanism sample drawn from that round's coin by inverse
CDF (`emPick`), so it has the law of Lemma B.4. There are no public coins. Line 3's `α` (and with it
`β` and the container constant `c`) is used only in the analysis, never by the algorithm, so it is not
a parameter of the protocol. A message is `⊥` or a subset of `W`; containers are subsets of `W_r` by
Lemma 4.5, so writing them inside `W` loses nothing. -/
noncomputable def algo3 (X : Finset (EuclideanSpace ℝ (Fin d))) (n t : ℕ) (ε : ℝ)
    (W : Finset (EuclideanSpace ℝ (Fin d)))
    (cont : Finset (EuclideanSpace ℝ (Fin d)) → Finset (Finset (EuclideanSpace ℝ (Fin d)))) :
    Protocol (Fin n → ↥X) Outcome where
  ΩA := Fin (rounds W) → ℝ
  ΩB := Fin (rounds W) → ℝ
  ΩP := Unit
  Msg := Algo3Msg W
  mM := ⊤
  μA := Measure.pi fun _ => volume.restrict (Set.Ico (0 : ℝ) 1)
  μB := Measure.pi fun _ => volume.restrict (Set.Ico (0 : ℝ) 1)
  μP := Measure.dirac ()
  nextA r S ω _ h :=
    if r / 2 < rounds W then
      release t ε W cont true S (coinAt ω (r / 2)) (activeSet (histAt none h) (r / 2))
    else none
  nextB r S ω _ h :=
    if r / 2 < rounds W then
      release t ε W cont false S (coinAt ω (r / 2)) (activeSet (histAt none h) (r / 2))
    else none
  stop r _ h := algo3Stop (rounds W) r (histAt none h)

end Supplement

end PrivOptTest


