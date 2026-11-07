-- Prove2me | Definitions.Def_CritWinSpin_Lhat
-- name    : CritWinSpin_Lhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:43.326882+00:00
-- url     : https://prove2.me/theorems/deb25362-df27-474d-8397-9263e4bcc981
-- title:
--   The procedure $\hat L_{T,k}$, slot kernels, decoding $Y$, the event Pass and the message $m^*$
-- statement:
--   A **slot kernel** gives for each binary input $y$ a law on $A^{N}\cup\{\bot\}$. The procedure $\hat L_{T,k}(F_{1:T})$ processes $t=1,\dots,T$ with independent slots of input $F_t$ and returns the first $k$ accepted outputs, or $\bot$ if fewer accept; the accepted indices are $i_1<\dots<i_k$. The decoding is $Y(\sigma)=(\mathrm{sign}\,M_1,\dots,\mathrm{sign}\,M_n)$ if no cloud is tied, and $\bot$ otherwise. The clause `LhatDecodes` says that on every run of positive probability $Y(X_j)=F_{i_j}$.
--
--   For $\Omega$ and $\Psi$, the event **Pass** on $X'_{1:k+1}$ requires $Y(X'_j)\in\Omega$ for all $j$ and pairwise distinct messages $\Psi(Y(X'_j))$. The message $m^*$ is that of the first coordinate of $X'$ whose decoded message is outside $S(X_{1:k})=\{\Psi(Y(X_j)):Y(X_j)\ne\bot\}$. The law `keyLiftLaw` is that of an instance $M(P)$ under KeyGen.
--
--   **Formalization Note** The procedure on p.24 stops at the $k$-th acceptance. Slots being independent, drawing all $T$ outcomes and keeping the first $k$ accepted gives the same output law; slots after the $k$-th acceptance are the slots "never reached" of §7. A slot machine's output is decoded through $[n]\times[r]\cong[nr]$.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §6.2, p.24; §7, p.26

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_PPT
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CritWinSpin_nuPm
import Definitions.Def_CritWinSpin_errExt
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc
set_option autoImplicit false

namespace CritWinSpin

/-- The first `k` accepted slots of a run `ω : [T] → A ∪ {⊥}`, with their indices `i_1 < ⋯ < i_k`, or
`none` if fewer than `k` slots accept (the procedure `L̂_{T,k}`, p.24).

**Formalization Note.** On p.24 the procedure stops at the `k`-th acceptance. The slots are
independent, so drawing all `T` slot outcomes and keeping the first `k` accepted ones has the same
output law; slots after the `k`-th acceptance are the slots "never reached" of §7, p.26. -/
def lhatRun {α : Type} {T : ℕ} (k : ℕ) (ω : Fin T → Option α) : Option (Fin k → Fin T × α) :=
  let l := (List.finRange T).filterMap fun t => (ω t).map fun a => (t, a)
  if h : k ≤ l.length then some fun j => l.get ⟨j, lt_of_lt_of_le j.2 h⟩ else none

open Classical in
/-- **The output law of `L̂_{T,k}(F_{1:T})`**, p.24, for a slot kernel `κ`: each input `F_t` is
processed by an independent slot with law `κ (F_t)` on `A ∪ {⊥}`; the output is the list of the first
`k` accepted slot outputs, or `⊥`.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), §6.2, p.24. -/
noncomputable def Lhat {α β : Type} [Fintype α] {T : ℕ} (κ : β → Option α → ℝ) (k : ℕ)
    (F : Fin T → β) (o : Option (Fin k → α)) : ℝ :=
  ∑ ω : Fin T → Option α, (∏ t, κ (F t) (ω t)) *
    if (lhatRun k ω).map (fun R j => (R j).2) = o then (1 : ℝ) else 0

/-- The law `L̂_{T,k}(μ^{⊗T})` on `(A^N)^k ∪ {⊥}` (eq. (37), p.25). -/
noncomputable def LhatMu {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (κ : β → Option α → ℝ)
    (μ : β → ℝ) (T k : ℕ) (o : Option (Fin k → α)) : ℝ :=
  ∑ F : Fin T → β, prodLaw μ F * Lhat κ k F o

/-- The decoding `Y(σ)`, p.24: the signs of the cloud sums if no cloud is tied, and `⊥` otherwise. -/
noncomputable def decodeY {S : SpinLaw} {n r : ℕ} (σ : Config S (Fin n × Fin r)) : Option (BinCfg n) :=
  open Classical in
  if tiedCount σ = 0 then some fun i => decide (0 < cloudSum σ i) else none

/-- The decoding clause of Theorem 6.3(ii), p.25: on every run of positive probability, whenever
`L̂_{T,k}(F_{1:T}) ≠ ⊥` its outputs decode to the inputs at the accepted indices, `Y(X_j) = F_{i_j}`. -/
def LhatDecodes {S : SpinLaw} {n r : ℕ}
    (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ) : Prop :=
  ∀ (T k : ℕ) (F : Fin T → BinCfg n) (ω : Fin T → Option (Config S (Fin n × Fin r))),
    (∀ t, 0 < κ (F t) (ω t)) → ∀ R, lhatRun k ω = some R →
      ∀ j : Fin k, decodeY (R j).2 = some (F (R j).1)

/-- Decoding of a slot machine's output in `A^{[n]×[r]}`, through `[n] × [r] ≅ [nr]`; any other string
is `⊥`. -/
noncomputable def decCloud (S : SpinLaw) (n r : ℕ) (s : Str) : Option (Config S (Fin n × Fin r)) :=
  (decConfig S (n * r) s).map fun x => x ∘ finProdFinEquiv

/-- The slot law of a PPT slot machine on input `(H, û, y)`, with the cloud size of (36), p.24. -/
noncomputable def slotKernel (S : SpinLaw) (p Cc : ℕ) (slotM : PPT) {n : ℕ} (H : Inst n) (û : ℚ)
    (y : BinCfg n) (o : Option (Config S (Fin n × Fin (cloudSize p Cc n)))) : ℝ :=
  open Classical in
  slotM.prob (tupleCode [encInst H, encRat û, List.ofFn y])
    (fun s => decCloud S n (cloudSize p Cc n) s = o)

/-- The decoded message `Ψ(Y(σ))`, or `⊥` (§7, p.26). -/
noncomputable def decMsg {S : SpinLaw} {n r d : ℕ} (Ψ : BinCfg n → Fin d → Bool)
    (σ : Config S (Fin n × Fin r)) : Option (Fin d → Bool) :=
  (decodeY σ).map Ψ

/-- The event `Pass`, p.26: all `k + 1` coordinates decode into `Ω`, with pairwise distinct messages. -/
def PassEv {S : SpinLaw} {n r d k : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (X' : Fin (k + 1) → Config S (Fin n × Fin r)) : Prop :=
  (∀ j, ∃ y, decodeY (X' j) = some y ∧ y ∈ Ω) ∧ Function.Injective fun j => decMsg Ψ (X' j)

open Classical in
/-- The message `m*`, p.26: the decoded message of the first coordinate of `X'` whose decoded message
is outside `S(X_{1:k}) = {Ψ(Y(X_j)) : Y(X_j) ≠ ⊥}`. -/
noncomputable def mStar {S : SpinLaw} {n r d k : ℕ} (Ψ : BinCfg n → Fin d → Bool)
    (X : Fin k → Config S (Fin n × Fin r)) (X' : Fin (k + 1) → Config S (Fin n × Fin r)) :
    Option (Fin d → Bool) :=
  (List.finRange (k + 1)).findSome? fun j =>
    match decMsg Ψ (X' j) with
    | some m => if ∃ j', decMsg Ψ (X j') = some m then none else some m
    | none => none

/-- The lifted instance law for Theorem 7.2, p.27: `(P, K) ← KeyGen(1^d)`, then `M = M(P)`. -/
noncomputable def keyLiftLaw (F : BilinearFamily) {N : ℕ} (d : ℕ)
    (M : (desc : Str) → WatersKey F desc d → Inst N) : InstLaw N :=
  open Classical in
  { supp := (Finset.univ.biUnion fun ω : Fin (F.gen.coins.eval (unary d).length) → Bool =>
      Finset.univ.image fun key =>
        M (F.gen.alg (tupleCode [List.ofFn ω, unary d])) key)
    prob := fun M₀ => keygenAvg F d fun desc key => if M desc key = M₀ then (1 : ℝ) else 0 }

end CritWinSpin


