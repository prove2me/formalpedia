-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Analysis
-- name    : QuantumBA_PackedShares_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:46.243529+00:00
-- url     : https://prove2.me/theorems/47e60b55-8520-4e06-aab4-1b2e9a626ec1
-- title:
--   Analysis notions: budgets, successful nodes, counted sets, the event 𝓔, marks, protection, latent values, fresh common coins (Definition 3.2)
-- statement:
--   Fix a parameter record, an input vector and an adversary; a *history* is a finite execution prefix, a *boundary* a micro-step index (it may lie inside a round), and $B_s$ the set of processes corrupted by $s$.
--
--   **Selection** (§3.3, §4.3). For node $v$ at level $\ell$: $e_v$ is the end of its last coin phase, $d_v$ the end of its delivery round ($=e_v$ at the root); $\mathrm{Bud}_v$ is $|C_v\cap B_{d_v}|\le\gamma|C_v|$ with $\gamma=1/3-\varepsilon/2$. Node $v$ is **successful** (Definition 3.1) if $\mathrm{Bud}_v$ holds and all members honest at $e_v$ output the same list $A_v$. $\mathrm{Good}=\{x\in[N]:\mathrm{dealer}(x)\notin B_{s_0}\}$ ($s_0$ the end of distribution), $G_0=\mathrm{Good}$, $G_\ell$ the identifiers of $G_{\ell-1}$ in the output of a successful level-$\ell$ node; $g_v=|G_{\ell-1}\cap I_v|$; $F_0=|\mathrm{Good}|/N$, $F_\ell=|G_\ell|/(m_\ell w)$. $\mathrm{Fail}_v$: the honest members at $e_v$ disagree, or fewer than $(g_v/r-\eta)w$ entries of the common output lie in $G_{\ell-1}$. $\mathcal E$: $\mathrm{Bud}_v\Rightarrow\neg\mathrm{Fail}_v$ whenever $g_v\ge\tau r$. $\xi=u2^{-\tau r}+be^{-\eta^2w/2}$, $\delta=\xi\sum_\ell m_\ell$, $p_n=\delta+2^{-w/2}$.
--
--   **Sharing** (§5.3). The circuit of a word: its dealer block and the transfer blocks of holders that transfer it, outputs going to the receivers' blocks or stored at the receivers. A block is exposed at $s$ if its holder is corrupted by $s$ and before the end of the block's round; marks are assigned backward: a stored register is marked if its holder is corrupted by $s$, a block if it is exposed or more than $\sigma(D)$ of its outputs are marked. A word is **protected** at $s$ if its dealer block is unmarked, and **unopened** if no honest holder has measured a register of it.
--
--   **Latent values** for a set $W$ of words after a history $h_0$: positive operators $\Lambda_h(s)$ on the adversary's system, $s\in F^W$, summing to $\mathbb P[h]\rho_{E|h}$ and consistent along histories, with (a) $\rho_{S_{W'}E|h}=q^{-|W'|}\sum_s|s\rangle\langle s|\otimes\rho_{E|h}$ for words $W'$ unopened at $h$ and (b) every requester honest through a reconstruction of $\omega$ obtains $S_\omega$.
--
--   **Fresh common coins** (Definition 3.2): conditional on every epoch-entry history preceding the first honest decision, for every node $v$ and every adversary under which $\mathrm{Bud}_v$ holds on every execution, the level-$\ell$ bin and coin words of the arrays of $G_{\ell-1}$ in $v$'s subtree are unopened at every history $h_0$ at the common deadline of level $\ell-1$ and have latent values with (a) strictly before the first honest decision and (b) for members of $C_v$; the same for the final words of $G_h$ after every selection history, with all processes as requesters.
--
--   The standing assumptions of §3–§5 on symbolic parameters (WellFormed), phases and procedures of ByzantineAgreementWithCommonCoin, and per-epoch costs are defined here as well.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, §3.3–3.4 (pp. 14–15, PDF 15–16), Definitions 3.1–3.2; §4.2–4.3 (pp. 18–20, PDF 19–21) and (3); §5.3 (pp. 25–26, PDF 26–27)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Protocol

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace QuantumBA.PackedShares

attribute [local instance] Classical.propDecidable

/-! # Analysis notions of §3.3–§3.4, §4 and §5.3 for QBA:PackedShares

All notions are functions of a classical history `h` (a finite execution prefix; boundaries are
micro-step indices, so a boundary may lie inside a round) for a fixed parameter set `X`, input
vector `x` and adversary `A`.  They are used only in the analysis. -/

section Analysis

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)

/-- Adversaries against QBA:PackedShares with parameters `X`. -/
abbrev Adv := Adversary n F (qba X).M (qba X).Hd

variable (x : Fin n → Bool) (A : Adv X)

/-- Configuration after the history `h`. -/
noncomputable def cfgH (h : History F) : Cfg n F (qba X) := (run (qba X) x A X.t h).1

/-- `B_s`: processes corrupted by the boundary `k` of the history `h` (`k ≤ |h|`). -/
noncomputable def badAt (h : History F) (k : ℕ) : Finset (Fin n) := (cfgH X x A (h.take k)).bad

/-- Local state (view) of `p` at boundary `k` of `h`. -/
noncomputable def viewAt (h : History F) (k : ℕ) (p : Fin n) : View n F := (cfgH X x A (h.take k)).st p

/-- `h` has positive probability. -/
def PosH (h : History F) : Prop := 0 < weight (qba X) x A X.t h

/-- The execution law. -/
noncomputable def μX : MeasureTheory.Measure (ℕ → Outcome F) := execMeasure (qba X) x A X.t

/-- Executions extending `h`. -/
def cyl (h : History F) : Set (ℕ → Outcome F) := {ω | prefixH ω h.length = h}

/-- `P[E | h]`. -/
noncomputable def condProb (h : History F) (E : Set (ℕ → Outcome F)) : ℝ≥0∞ :=
  μX X x A (E ∩ cyl h) / μX X x A (cyl h)

/-- Boundary at the end of global round `R`. -/
def bnd (n R : ℕ) : ℕ := endOfRound n R

/-- Boundary at the start of global round `R` (= end of round `R - 1`). -/
def startB (n R : ℕ) : ℕ := R * stepsPerRound n

/-- `p` is active (honest, not halted) at the start of global round `R` (so it performs the
round's honest step unless corrupted before it). -/
noncomputable def ActiveAtStart (h : History F) (R : ℕ) (p : Fin n) : Prop :=
  p ∉ badAt X x A h (startB n R) ∧ (qba X).halted (viewAt X x A h (startB n R) p) = false

/-- No process has decided while honest at any boundary up to the end of `h`: `h` lies strictly
before `s_dec`, the boundary of the first honest decision. -/
noncomputable def NoHonDec (h : History F) : Prop :=
  ∀ k ≤ h.length, ∀ p, p ∉ badAt X x A h k → (qba X).decision (viewAt X x A h k p) = none

/-! ## Epoch boundaries, budgets, successful nodes, counted sets (§3.3, §4.3) -/

/-- Entry boundary of epoch `e`. -/
noncomputable def epochStart (e : ℕ) : ℕ := startB n (gRound X e 0)

/-- `s₀`: end of distribution of epoch `e`. -/
noncomputable def distEnd (e : ℕ) : ℕ := bnd n (gRound X e 0)

/-- `e_v`: boundary at which the members of a level-`ℓ` node produce their output lists (end of
the last coin phase). -/
noncomputable def outB (e ℓ : ℕ) : ℕ := bnd n (gRound X e (lvlStart X ℓ + 1 + 4 * X.r))

/-- `d_v`: end of the delivery round of level `ℓ` (`= e_v` at the root); for `ℓ = 0` the end of
distribution.  This is the common deadline of level `ℓ`. -/
noncomputable def delB (e ℓ : ℕ) : ℕ :=
  if ℓ = 0 then distEnd X e else if ℓ = X.h then outB X e ℓ else bnd n (gRound X e (deliveryRound X ℓ))

/-- `γ = 1/3 - ε/2`. -/
noncomputable def gam : ℝ := 1 / 3 - X.ε / 2

/-- `Bud_v`: `|C_v ∩ B_{d_v}| ≤ γ|C_v|`. -/
noncomputable def Bud (h : History F) (e ℓ i : ℕ) : Prop :=
  (((X.comm ℓ i) ∩ badAt X x A h (delB X e ℓ)).card : ℝ) ≤ gam X * (X.comm ℓ i).card

/-- Output list of `p` for node `(ℓ, i)` (read from its view at `e_v`). -/
noncomputable def outputOf (h : History F) (e ℓ i : ℕ) (p : Fin n) : List ℕ :=
  outsE X (viewAt X x A h (outB X e ℓ) p) e ℓ i

/-- All members of `C_v` honest at `e_v` output the list `L`. -/
noncomputable def AllOutput (h : History F) (e ℓ i : ℕ) (L : List ℕ) : Prop :=
  ∀ p ∈ X.comm ℓ i, p ∉ badAt X x A h (outB X e ℓ) → outputOf X x A h e ℓ i p = L

/-- Definition 3.1: node `v` is successful if `Bud_v` holds and all members honest at `e_v`
output the same normalized list. -/
noncomputable def Successful (h : History F) (e ℓ i : ℕ) : Prop :=
  Bud X x A h e ℓ i ∧ ∃ L, AllOutput X x A h e ℓ i L

/-- The common output list `A_v` (if the honest members agree; otherwise empty). -/
noncomputable def commonList (h : History F) (e ℓ i : ℕ) : List ℕ :=
  if hL : ∃ L, AllOutput X x A h e ℓ i L then hL.choose else []

/-- `Good = {x ∈ [N] : dealer(x) ∉ B_{s₀}}`. -/
noncomputable def Good (h : History F) (e : ℕ) : Finset ℕ :=
  ((Finset.range X.N).image (· + 1)).filter (fun y => ∀ hd : dealer n y < n,
    (⟨dealer n y, hd⟩ : Fin n) ∉ badAt X x A h (distEnd X e))

/-- Counted sets: `G₀ = Good`, `G_ℓ` = identifiers of `G_{ℓ-1}` in the output of a successful
level-`ℓ` node. -/
noncomputable def Gset (h : History F) (e : ℕ) : ℕ → Finset ℕ :=
  fun ℓ0 => Nat.rec (motive := fun _ => Finset ℕ) (Good X x A h e)
    (fun ℓ G => G.filter (fun y => ∃ i < X.m (ℓ + 1),
      Successful X x A h e (ℓ + 1) i ∧ y ∈ commonList X x A h e (ℓ + 1) i)) ℓ0

/-- `g_v`: number of counted inputs of node `(ℓ, i)` (positions holding an identifier of
`G_{ℓ-1}`; identifiers are distinct, so this is `|G_{ℓ-1} ∩ I_v|`). -/
noncomputable def gcount (h : History F) (e ℓ i : ℕ) : ℕ :=
  ((Gset X x A h e (ℓ - 1)).filter (fun y => inInterval X ℓ i y)).card

/-- `F₀ = |Good|/N`, `F_ℓ = |G_ℓ|/(m_ℓ w)`. -/
noncomputable def Fval (h : History F) (e ℓ : ℕ) : ℝ :=
  if ℓ = 0 then ((Good X x A h e).card : ℝ) / X.N
  else ((Gset X x A h e ℓ).card : ℝ) / ((X.m ℓ : ℝ) * X.w)

/-- `Fail_v`: the members honest at `e_v` output different lists, or fewer than `(g/r - η)w`
entries of the common output lie in `G_{ℓ-1}`. -/
noncomputable def Fail (η : ℝ) (h : History F) (e ℓ i : ℕ) : Prop :=
  (¬ ∃ L, AllOutput X x A h e ℓ i L) ∨
  ((((commonList X x A h e ℓ i).filter (fun y => y ∈ Gset X x A h e (ℓ - 1))).length : ℝ) <
    ((gcount X x A h e ℓ i : ℝ) / X.r - η) * X.w)

/-- The event `𝓔` of (3): `Bud_v ⇒ ¬Fail_v` for every node `v` with `g_v ≥ τr`. -/
noncomputable def EventE (τ η : ℝ) (h : History F) (e : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h → ∀ i < X.m ℓ, τ * X.r ≤ gcount X x A h e ℓ i →
    Bud X x A h e ℓ i → ¬ Fail X x A η h e ℓ i

/-- The hypothesis of Lemma 4.5: for the realized fault set at each level's common deadline, at
most `βm_ℓ` level-`ℓ` budgets fail. -/
noncomputable def FewOverloaded (β : ℝ) (h : History F) (e : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h →
    (((Finset.range (X.m ℓ)).filter (fun i => ¬ Bud X x A h e ℓ i)).card : ℝ) ≤ β * X.m ℓ

/-- `ξ = u 2^{-τr} + b e^{-η²w/2}` of (2). -/
noncomputable def xi (τ η : ℝ) : ℝ :=
  X.u * (2 : ℝ) ^ (-(τ * X.r)) + X.b * Real.exp (-(η ^ 2 * X.w / 2))

/-- `δ = ξ ∑_{ℓ=1}^h m_ℓ` of (3). -/
noncomputable def deltaP (τ η : ℝ) : ℝ := xi X τ η * ∑ ℓ ∈ Finset.Icc 1 X.h, (X.m ℓ : ℝ)

/-- `p_n = δ + 2^{-w/2}` (Lemma 4.8). -/
noncomputable def pn (τ η : ℝ) : ℝ := deltaP X τ η + (2 : ℝ) ^ (-((X.w : ℝ) / 2))

/-! ## The sharing scheme: circuits, marks, protection, openings, reconstructions (§5.3) -/

/-- Global round of the block of level `j` (`j = 0`: dealer block in the distribution round;
`j ≥ 1`: transfer block in the delivery round of level `j`). -/
noncomputable def blockRound (e j : ℕ) : ℕ := if j = 0 then gRound X e 0 else gRound X e (deliveryRound X j)

/-- The block of holder `u` at level `j ≥ 1` for word `(y, λ)` of epoch `e` belongs to the
circuit at boundary `s`: its round has begun by `s` and `u`, active at the start of that round,
transfers the word (it lies in `u`'s own output list). -/
noncomputable def BlockAt (h : History F) (s e y : ℕ) (lb : Lbl) (j : ℕ) (u : Fin n) : Prop :=
  startB n (blockRound X e j) < s ∧ ActiveAtStart X x A h (blockRound X e j) u ∧
  (y, lb) ∈ transferWords X (viewAt X x A h (startB n (blockRound X e j)) u)
    (outsE X (viewAt X x A h (startB n (blockRound X e j)) u) e j) j

/-- The dealer block of word `(y, λ)` belongs to the circuit at `s`. -/
noncomputable def DealerBlockAt (h : History F) (s e y : ℕ) (lb : Lbl) : Prop :=
  ∃ hd : dealer n y < n, startB n (gRound X e 0) < s ∧
    ActiveAtStart X x A h (gRound X e 0) ⟨dealer n y, hd⟩ ∧
    (y, lb) ∈ distWords X (viewAt X x A h (startB n (gRound X e 0)) ⟨dealer n y, hd⟩)

/-- A block of holder `u` with round `R` is exposed at `s`: `u` is corrupted by `s` and before the
end of the block's round. -/
noncomputable def Exposed (h : History F) (s R : ℕ) (u : Fin n) : Prop :=
  u ∈ badAt X x A h (min s (bnd n R))

/-- Marks at boundary `s` (taken backward from the stored registers): `markedT h s e y λ d u`
says that the transfer block of holder `u` at level `X.h - d` is marked, by recursion on `d`.
An output of block `(j, u)` sent to `u'` is marked if it is the input of a marked block
`(j+1, u')` of its holder, or, if it is not an input of a block of the circuit, if its holder
`u'` is corrupted by `s` (a marked stored register).  A block is marked if it is in the circuit
and is exposed or has more than `σ(D)` marked outputs. -/
noncomputable def markedT (h : History F) (s e y : ℕ) (lb : Lbl) : ℕ → Fin n → Prop :=
  fun d0 => Nat.rec (motive := fun _ => Fin n → Prop)
    (fun _ => False)
    (fun d markedAbove u =>
      let j := X.h - (d + 1)
      let outM : Fin n → Prop := fun u' =>
        if BlockAt X x A h s e y lb (j + 1) u' ∧ u ∈ (inNbrs X j y u').take (X.p (j + 1)) ∧
            1 ≤ j + 1 ∧ j + 1 ≤ X.h - d
        then markedAbove u' else u' ∈ badAt X x A h s
      BlockAt X x A h s e y lb j u ∧
        (Exposed X x A h s (blockRound X e j) u ∨
          X.sigma (nbrs X j y u).length < ((nbrs X j y u).filter (fun u' => outM u')).length))
    d0

/-- The transfer block `(j, u)` is marked at `s`. -/
noncomputable def MarkedBlock (h : History F) (s e y : ℕ) (lb : Lbl) (j : ℕ) (u : Fin n) : Prop :=
  1 ≤ j ∧ j ≤ X.h ∧ markedT X x A h s e y lb (X.h - j + 1) u

/-- Word `(y, λ)` of epoch `e` is protected at boundary `s`: its dealer block is in the circuit and
unmarked (not exposed, and at most `σ(k₁)` of its outputs to `C₁(y)` are marked). -/
noncomputable def Protected (h : History F) (s e y : ℕ) (lb : Lbl) : Prop :=
  DealerBlockAt X x A h s e y lb ∧
  ∀ hd : dealer n y < n, ¬ (Exposed X x A h s (gRound X e 0) ⟨dealer n y, hd⟩ ∨
    X.sigma (sortedMembers (stageComm X y 1)).length <
      ((sortedMembers (stageComm X y 1)).filter (fun u' =>
        if BlockAt X x A h s e y lb 1 u' then MarkedBlock X x A h s e y lb 1 u'
        else u' ∈ badAt X x A h s)).length)

/-- Registers of word `(y, λ)` (at its stage of use) measured by `p` in global round `R`
(a holder honest and active at the round's honest step measures them in the computational
basis). -/
noncomputable def MeasuresWord (h : History F) (R e y : ℕ) (lb : Lbl) (p : Fin n) : Prop :=
  let k := startB n R + (n + 1)
  let V := viewAt X x A h k p
  p ∉ badAt X x A h k ∧ (qba X).halted V = false ∧ R / X.epochLen = e ∧
    ∃ r ∈ qbaMeas X V, r ∈ (storedUse X V (outsE X V e) e y lb).map Prod.snd

/-- Word `(y, λ)` is unopened at boundary `s`: no honest holder has measured a register of it by
then. -/
noncomputable def Unopened (h : History F) (s e y : ℕ) (lb : Lbl) : Prop :=
  ∀ R, startB n R + (n + 1) < s → ∀ p, ¬ MeasuresWord X x A h R e y lb p

/-- Value obtained by requester `q` from a reconstruction of word `(y, λ)` completed at the end of
global round `R` (the reply round of its request), if `q`'s schedule reconstructs that word in
round `R`: bin words of its provider lists in the bin reply round, the coin word of position `j`
in the reply round of phase `j`, the final word of position `j` of its root list in final phase
`j ≤ w`. -/
noncomputable def ReconValue (V : View n F) (e R y : ℕ) (lb : Lbl) : Option F :=
  let outs := outsE X V e
  match lb with
  | .bin ℓ =>
    if ∃ i ∈ myNodes X V ℓ, y ≠ 0 ∧ y ∈ provList X V e ℓ i ∧ R = gRound X e (lvlStart X ℓ + 1)
    then (if hi : ∃ i ∈ myNodes X V ℓ, y ≠ 0 ∧ y ∈ provList X V e ℓ i then
        some (reconstruct X V outs e R ℓ hi.choose y lb) else none) else none
  | .coin ℓ =>
    if hi : ∃ i ∈ myNodes X V ℓ, ∃ j, 1 ≤ j ∧ j ≤ X.r ∧ y ≠ 0 ∧ (provList X V e ℓ i).getD (j - 1) 0 = y ∧
        R = gRound X e (lvlStart X ℓ + 2 + 4 * (j - 1) + 3)
    then some (reconstruct X V outs e R ℓ hi.choose y lb) else none
  | .final =>
    if ∃ j, 1 ≤ j ∧ j ≤ X.w ∧ y ≠ 0 ∧ (rootList X V e).getD (j - 1) 0 = y ∧ R = gRound X e (finStart X j + 3)
    then some (reconstruct X V outs e R 0 0 y lb) else none

/-- Positive semidefiniteness (and Hermiticity) of a kernel on the registers `r < m` satisfying
`keep r` (other coordinates fixed to `0`). -/
def IsPSDOn (keep : ℕ → Prop) (m : ℕ) (K : QState F) : Prop :=
  (∀ a b : Fin m → F, (∀ i, ¬ keep i.1 → a i = 0) → (∀ i, ¬ keep i.1 → b i = 0) →
      K (extN m a) (extN m b) = star (K (extN m b) (extN m a))) ∧
  ∀ φ : (Fin m → F) → ℂ, 0 ≤ (∑ a : Fin m → F, ∑ b : Fin m → F,
    (if (∀ i, ¬ keep i.1 → a i = 0) ∧ (∀ i, ¬ keep i.1 → b i = 0) then
      star (φ a) * K (extN m a) (extN m b) * φ b else 0)).re

/-- Trace over the registers `r < m` with `keep r`. -/
noncomputable def traceOn (keep : ℕ → Prop) (m : ℕ) (K : QState F) : ℂ :=
  ∑ a : Fin m → F, if ∀ i, ¬ keep i.1 → a i = 0 then K (extN m a) (extN m a) else 0

/-- Registers the adversary holds after `h` (its memory and the registers of corrupted
processes, including registers seized in transit). -/
noncomputable def advReg (h : History F) (r : ℕ) : Prop := (cfgH X x A h).accessible r

/-- `P[h] ρ_{E|h}`: the unnormalized state of the adversary's quantum system on the branch of `h`
(partial trace of the branch state over all registers it does not hold). -/
noncomputable def advState (h : History F) : QState F :=
  let m := (cfgH X x A h).next
  let ρ := (run (qba X) x A X.t h).2
  fun a b => ∑ z : Fin m → F, if ∀ i, advReg X x A h i.1 → z i = 0 then
    ρ (fun j => if hj : j < m ∧ ¬ advReg X x A h j then z ⟨j, hj.1⟩ else a j)
      (fun j => if hj : j < m ∧ ¬ advReg X x A h j then z ⟨j, hj.1⟩ else b j) else 0

/-- **Latent values** (§5.3, Definition 3.2, Lemma 5.2) for a finite set `W` of words of epoch
`e`, on the executions extending `h₀`: a family `Λ h s` (for histories `h` extending `h₀` and
values `s : W → F`) of positive operators on the adversary's system with
`∑_s Λ h s = P[h] ρ_{E|h}`, consistent along histories (so `P[S = s, h] = Tr Λ h s` is a
joint law of the latent values `S` and the execution), such that
(a) at every history `h` with `allowedH h`, for every set `W'` of words still unopened at `h`,
`ρ_{S_{W'} E | h} = q^{-|W'|} ∑_s |s⟩⟨s| ⊗ ρ_{E|h}`; and
(b) every requester `q` with `allowedR q R`, honest through a reconstruction of `ω ∈ W` completed
at the end of round `R` (with `allowedH` at that boundary), obtains `S_ω`. -/
noncomputable def LatentValues (h₀ : History F) (e : ℕ) (W : Finset (ℕ × Lbl))
    (allowedH : History F → Prop) (allowedR : Fin n → ℕ → Prop) : Prop :=
  ∃ Λ : History F → (W → F) → QState F,
    (∀ h, h₀ <+: h → ∀ s, IsPSDOn (advReg X x A h) (cfgH X x A h).next (Λ h s)) ∧
    (∀ h, h₀ <+: h → (fun a b => ∑ s, Λ h s a b) = advState X x A h) ∧
    (∀ h, h₀ <+: h → ∀ s,
      (∑' o, ENNReal.ofReal (traceOn (advReg X x A (h ++ [o])) (cfgH X x A (h ++ [o])).next
          (Λ (h ++ [o]) s)).re) =
        ENNReal.ofReal (traceOn (advReg X x A h) (cfgH X x A h).next (Λ h s)).re) ∧
    (∀ h, h₀ <+: h → allowedH h → ∀ W' : Finset (ℕ × Lbl), ∀ hW : W' ⊆ W,
      (∀ wd ∈ W', Unopened X x A h h.length e wd.1 wd.2) →
      ∀ s' : W' → F,
        (fun a b => ∑ s : W → F, if (∀ wd : W', s ⟨wd.1, Finset.mem_of_subset hW wd.2⟩ = s' wd)
          then Λ h s a b else 0) =
        fun a b => ((Fintype.card F : ℂ) ^ W'.card)⁻¹ * advState X x A h a b) ∧
    (∀ h R q, h₀ <+: h → h.length = bnd n R → allowedH h → allowedR q R →
      q ∉ badAt X x A h h.length → ∀ wd : W, ∀ v,
        ReconValue X (viewAt X x A h h.length q) e R wd.1.1 wd.1.2 = some v →
        ∀ s : W → F, s wd ≠ v → Λ h s = 0)

/-- Definition 3.2 (**fresh common coins**) for QBA:PackedShares with parameters `X`: for every
input vector and adversary, conditional on every epoch-entry history preceding the first honest
decision: (1) for every level-`ℓ` node `v`, if `Bud_v` holds on every execution extending the
entry history, then for every history `h₀` at the common deadline of level `ℓ - 1` (end of
distribution if `ℓ = 1`), the level-`ℓ` bin and coin words of the arrays of `G_{ℓ-1}` in `v`'s
subtree are unopened at `h₀` and have latent values, with (a) at histories strictly before
`s_dec` and (b) for members of `C_v` and reconstructions completed strictly before `s_dec`;
(2) the same holds for the final words of `G_h` after every selection history (the end of
distribution if `h = 0`), with all processes as requesters and under every adversary. -/
noncomputable def FreshCoins : Prop :=
  ∀ (x : Fin n → Bool) (A : Adv X) (e : ℕ) (he : History F),
    he.length = epochStart X e → PosH X x A he → NoHonDec X x A he →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h → ∀ i < X.m ℓ,
      (∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω he.length = he →
        Bud X x A (prefixH ω (delB X e ℓ)) e ℓ i) →
      ∀ h₀, he <+: h₀ → h₀.length = delB X e (ℓ - 1) → PosH X x A h₀ →
        let W : Finset (ℕ × Lbl) :=
          ((Gset X x A h₀ e (ℓ - 1)).filter (fun y => inInterval X ℓ i y)).biUnion
            (fun y => {(y, Lbl.bin ℓ), (y, Lbl.coin ℓ)})
        (∀ wd ∈ W, Unopened X x A h₀ h₀.length e wd.1 wd.2) ∧
        LatentValues X x A h₀ e W (NoHonDec X x A) (fun q _ => q ∈ X.comm ℓ i)) ∧
    (∀ h₀, he <+: h₀ → h₀.length = delB X e X.h → PosH X x A h₀ →
      let W : Finset (ℕ × Lbl) := (Gset X x A h₀ e X.h).image (fun y => (y, Lbl.final))
      (∀ wd ∈ W, Unopened X x A h₀ h₀.length e wd.1 wd.2) ∧
      LatentValues X x A h₀ e W (NoHonDec X x A) (fun _ _ => True))

/-! ## Standing assumptions of §3–§5 on the symbolic parameters -/

/-- The standing assumptions of §1.1, §3.1, §5.1–§5.2 on symbolic parameters: `0 < ε < 1/3`,
`t ≤ (1/3 - ε)n`; `b ≥ 2` and `w` powers of two; `|F| = q = 2^d` with `d = ⌈log₂(n+1)⌉`;
distinct nonzero evaluation points, nonzero `ψ`; each committee of level `ℓ ∈ [1, h]` has `k_ℓ ≤ n`
members and equals `P` iff `k_ℓ = n`; committee sizes are nondecreasing toward the root, whose
committee is `P`; at a level with transfers, every member has `D_ℓ` distinct forwarding
neighbours in the parent committee, and every parent member has in-degree at most `J ≥ 1`. -/
def WellFormed : Prop :=
  0 < X.ε ∧ X.ε < 1 / 3 ∧ (X.t : ℝ) ≤ (1 / 3 - X.ε) * n ∧
  2 ≤ X.b ∧ (∃ i, X.b = 2 ^ i) ∧ (∃ i, X.w = 2 ^ i) ∧
  Fintype.card F = 2 ^ parDbits n ∧ Function.Injective X.cf.α ∧ (∀ i, X.cf.α i ≠ 0) ∧ X.cf.ψ ≠ 0 ∧
  (∀ ℓ, 1 ≤ ℓ → ℓ ≤ X.h → X.k ℓ ≤ n ∧ ∀ i < X.m ℓ, (X.comm ℓ i).card = X.k ℓ ∧
      (X.comm ℓ i = Finset.univ ↔ X.k ℓ = n)) ∧
  (∀ ℓ, 1 ≤ ℓ → ℓ < X.h → X.k ℓ ≤ X.k (ℓ + 1)) ∧ (1 ≤ X.h → X.k X.h = n) ∧
  1 ≤ X.J ∧
  (∀ ℓ, 1 ≤ ℓ → ℓ < X.h → X.k ℓ < n → ∀ i < X.m ℓ,
    (∀ s ∈ X.comm ℓ i, (X.fwd ℓ i s).Nodup ∧ (X.fwd ℓ i s).length = X.D ℓ ∧
      ∀ u ∈ X.fwd ℓ i s, u ∈ X.comm (ℓ + 1) (i / X.b)) ∧
    ∀ u ∈ X.comm (ℓ + 1) (i / X.b), ((X.comm ℓ i).filter (fun s => u ∈ X.fwd ℓ i s)).card ≤ X.J)

/-- Properties (i)–(iii) of Lemma 5.3, for sampler error `ρ`, of the forwarding graph from
`C_{(ℓ,i)}` (rows) to its parent committee (columns), for a level with transfers. -/
noncomputable def FwdGraphProps (ρ : ℝ) (ℓ i : ℕ) : Prop :=
  let U := X.comm ℓ i
  let V := X.comm (ℓ + 1) (i / X.b)
  let D := X.D ℓ
  (∀ s ∈ U, (X.fwd ℓ i s).Nodup ∧ (X.fwd ℓ i s).length = D ∧ ∀ u ∈ X.fwd ℓ i s, u ∈ V) ∧
  (∀ v ∈ V, ((U.filter (fun s => v ∈ X.fwd ℓ i s)).card : ℤ) ≤ Jgraph n U.card V.card D) ∧
  (∀ Z ⊆ V, ((U.filter (fun s => (((X.fwd ℓ i s).filter (· ∈ Z)).length : ℝ) / D >
      (Z.card : ℝ) / V.card + ρ)).card : ℝ) ≤ ρ * U.card)

/-! ## Costs of one epoch (§6.4) and epochs through the last correct halt (Corollary 4.9) -/

/-- Qubits charged in the rounds of epoch `e` on the execution `ω`. -/
noncomputable def epochQ (ω : ℕ → Outcome F) (e : ℕ) : ℕ :=
  ∑ ρ ∈ Finset.range X.epochLen, (cfgAt (qba X) x A X.t ω (endOfRound n (gRound X e ρ))).roundQ

/-- Classical bits charged in the rounds of epoch `e` on the execution `ω`. -/
noncomputable def epochC (ω : ℕ → Outcome F) (e : ℕ) : ℕ :=
  ∑ ρ ∈ Finset.range X.epochLen, (cfgAt (qba X) x A X.t ω (endOfRound n (gRound X e ρ))).roundC

/-- Number of epochs entered through the last correct halt: `⌈R / (rounds per epoch)⌉`. -/
noncomputable def epochsThroughHalt (ω : ℕ → Outcome F) : ℕ∞ :=
  ⨅ (E : ℕ) (_ : roundsR (qba X) x A X.t ω ≤ (E * X.epochLen : ℕ)), (E : ℕ∞)

/-- Sampler property (10) of Lemma 5.3 (iii) for the forwarding graph out of `C_{(ℓ,i)}`. -/
noncomputable def SamplerProp (ρ : ℝ) (ℓ i : ℕ) : Prop :=
  let U := X.comm ℓ i
  let V := X.comm (ℓ + 1) (i / X.b)
  ∀ Z ⊆ V, ((U.filter (fun s => (((X.fwd ℓ i s).filter (· ∈ Z)).length : ℝ) / X.D ℓ >
      (Z.card : ℝ) / V.card + ρ)).card : ℝ) ≤ ρ * U.card

/-! ## Phases of ByzantineAgreementWithCommonCoin (Algorithm 3), in elections and in final
agreement -/

/-- A phase of ByzantineAgreementWithCommonCoin: phase `j` of the election of node `(ℓ, i)` in
epoch `e`, or final phase `g` (0-based across epochs). -/
inductive PhaseRef where
  | comm : ℕ → ℕ → ℕ → ℕ → PhaseRef
  | fin : ℕ → PhaseRef

/-- Members of the committee running the phase. -/
noncomputable def PhaseRef.members : PhaseRef → Finset (Fin n)
  | .comm _ ℓ i _ => X.comm ℓ i
  | .fin _ => Finset.univ

/-- Threshold `a` (`a_C` in elections, `t` in final agreement). -/
noncomputable def PhaseRef.thr : PhaseRef → ℕ
  | .comm _ ℓ i _ => aThr (X.comm ℓ i).card
  | .fin _ => X.t

/-- Number of components (`u` in elections, `1` in final agreement). -/
noncomputable def PhaseRef.width : PhaseRef → ℕ
  | .comm _ _ _ _ => X.u
  | .fin _ => 1

/-- Global round of round 1 of the phase. -/
noncomputable def PhaseRef.r1 : PhaseRef → ℕ
  | .comm e ℓ _ j => gRound X e (lvlStart X ℓ + 2 + 4 * (j - 1))
  | .fin g => finalPhaseRound X g

/-- Estimate vector of a member at the start of the phase (read from its view). -/
noncomputable def estStart (V : View n F) : PhaseRef → List Bool
  | .comm e ℓ i j => (elect X V (outsE X V e) (outsE X V e) e ℓ i).2.1 (j - 1)
  | .fin g => [(finalRun X V g).1]

/-- Estimate vector of a member at the end of the phase. -/
noncomputable def estEnd (V : View n F) : PhaseRef → List Bool
  | .comm e ℓ i j => (elect X V (outsE X V e) (outsE X V e) e ℓ i).2.1 j
  | .fin g => [(finalRun X V (g + 1)).1]

/-- Proposal vector of a member in the phase (Algorithm 3, line 3). -/
noncomputable def propV (V : View n F) : PhaseRef → List (Option Bool)
  | .comm e ℓ i j => (elect X V (outsE X V e) (outsE X V e) e ℓ i).2.2 j
  | .fin g => [finalY X V g]

/-- Forced vector of a member in the phase (Algorithm 3, line 5): `v` where at least `a + 1`
proposals (its own and the first well-formed proposal of each other member) equal `v`. -/
noncomputable def forcedV (V : View n F) (pr : PhaseRef) : List (Option Bool) :=
  let others := ((PhaseRef.members X pr).sort (· ≤ ·)).filter (· ≠ V.me)
  let tag : ℕ × ℕ × ℕ := match pr with
    | .comm _ ℓ i j => (ℓ, i, j)
    | .fin g => (0, 0, g % (X.w + 1) + 1)
  let votes := propV X V pr :: others.map (fun m =>
    ((firstFrom (V.cin (PhaseRef.r1 X pr + 1)) (fun msg => match msg with
      | .prop l i' j' v => if (l, i', j') = tag ∧ v.length = PhaseRef.width X pr then some v else none
      | _ => none) m).getD []))
  (List.range (PhaseRef.width X pr)).map (thrVote votes (PhaseRef.thr X pr + 1))

/-- Coin bit decoded by a member in the phase (Algorithm 3, line 7). -/
noncomputable def coinV (V : View n F) : PhaseRef → Bool
  | .comm e ℓ i j =>
    let Y := (elect X V (outsE X V e) (outsE X V e) e ℓ i).1
    coinOf X.cf (reconstruct X V (outsE X V e) e (gRound X e (lvlStart X ℓ + 2 + 4 * (j - 1)) + 3)
      ℓ i (Y.getD (j - 1) 0) (.coin ℓ))
  | .fin g =>
    let e := g / (X.w + 1)
    let j := g % (X.w + 1) + 1
    if j ≤ X.w then coinOf X.cf (reconstruct X V (outsE X V e) e (finalPhaseRound X g + 3) 0 0
      ((rootList X V e).getD (j - 1) 0) .final) else false

/-- `p` participates in the phase at boundary `k` of `h`: it is a member, honest and not halted. -/
noncomputable def Participates (h : History F) (k : ℕ) (pr : PhaseRef) (p : Fin n) : Prop :=
  p ∈ PhaseRef.members X pr ∧ p ∉ badAt X x A h k ∧ (qba X).halted (viewAt X x A h k p) = false

/-- A procedure (one run of Algorithm 3): the election of node `(ℓ, i)` in epoch `e` (phases
`1, …, r`), or the final agreement of epoch `e` (final phases `1, …, w + 1`). -/
inductive ProcRef where
  | elect : ℕ → ℕ → ℕ → ProcRef
  | final : ℕ → ProcRef

/-- Number of phases of the procedure. -/
noncomputable def ProcRef.numPhases : ProcRef → ℕ
  | .elect _ _ _ => X.r
  | .final _ => X.w + 1

/-- Phase `j ≥ 1` of the procedure. -/
noncomputable def ProcRef.phase : ProcRef → ℕ → PhaseRef
  | .elect e ℓ i, j => .comm e ℓ i j
  | .final e, j => .fin (e * (X.w + 1) + (j - 1))

end Analysis

end QuantumBA.PackedShares


