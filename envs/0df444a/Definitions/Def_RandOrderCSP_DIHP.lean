-- Prove2me | Definitions.Def_RandOrderCSP_DIHP
-- name    : RandOrderCSP_DIHP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:52.541451+00:00
-- url     : https://prove2.me/theorems/d53c584c-9ae8-4df8-a0bf-9e91ced53828
-- title:
--   The DIHP game and one-way blackboard protocols
-- statement:
--   In the game $\mathrm{DIHP}_{\Phi_*}(\alpha,T,n)$ for a gadget $\Phi_*=(G_*,\mathcal Y_*)$, the $t$-th of $T$ players receives $(H_t,Z_t)$. Independently for each $t$, $(H_t,\mathcal Y_t)\sim\mathrm{Poi}(\Phi_*^n,\alpha n^{-(k-1)})$. In the YES case a hidden signal $\mathbf X$ is uniform on $\mathbb Z_q^{\mathcal V_{G_*^n}}$ and $Z_t\sim T_{\Phi_t}(\mathbf X)$; in the NO case $Z_t$ is uniform.
--
--   A deterministic **protocol** has the players write in turn: each message is a function of the player's input and the board, and each $H_t$ is written for free. The output is a function of the board, the cost is the maximum total message length over all inputs, and the advantage is $|\mathbb P[\text{YES}\mid\text{YES case}]-\mathbb P[\text{YES}\mid\text{NO case}]|$.
--
--   The module also defines the objects of the reduction: $K_t$, the copies with an all-zero label row; the probability that a uniform injective choice lies over given edges; the probabilities $p_e$; and the joint probabilities of counts and chosen edges.
--
--   **Formalization Note** Joint laws are mass functions on the countable input space, summed in $[0,\infty]$. Messages are bit strings of arbitrary length.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Definition 4.3, §4.2, p.17; §4.3, p.19

import Mathlib
import Definitions.Def_RandOrderCSP_blowup
import Definitions.Def_RandOrderCSP_poiLaw
import Definitions.Def_RandOrderCSP_obsKernel

open MeasureTheory

namespace RandOrderCSP

/-- The input `(H_t, Z_t)` of a DIHP player: the count vector `c` of the sparsification of `G^n` (so
`H_t` has edge set `Σ e, Fin (c e)`) and a label matrix `Z_t ∈ ℤ_q^{ℰ_{H_t}×[k]}` (Definition 4.3). -/
abbrev PlayerInput (k q n : ℕ) (E : Type) : Type :=
  Σ c : E × (Fin k → Fin n) → ℕ, (Σ e, Fin (c e)) × Fin k → ZMod q

variable {k q n : ℕ} {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [NeZero q]

/-- The law of one player's input (Definition 4.3, items 1–3). `lab = some X` is the YES case
conditioned on the hidden signal `𝐗 = X`: `H ∼ Poi(G^n, αn^{-(k-1)})` and `Z ∼ T_Φ(X)`. `lab = none` is
the NO case: the same `H` and `Z` uniform on `ℤ_q^{ℰ_H×[k]}`. -/
noncomputable def playerMass (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n : ℕ)
    (lab : Option (V × Fin n → ZMod q)) (I : PlayerInput k q n E) : ENNReal :=
  poiLaw (E × (Fin k → Fin n)) (poiRate α n k) {I.1} *
    match lab with
    | some X => ENNReal.ofReal
        (obsKernel (sparsify (blowup G n) I.1) (sparsifyColor (blowupColor Y n) I.1) X I.2)
    | none => ENNReal.ofReal (1 / (q : ℝ) ^ (k * ∑ e, I.1 e))

/-- The law of the tuple `(H_t, Z_t)_{t ∈ [T]}` in the YES case, as a mass function: `𝐗` uniform on
`ℤ_q^{𝒱_{G^n}}`, and given `𝐗` the players' inputs are independent. -/
noncomputable def yesMass (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n T : ℕ)
    (I : Fin T → PlayerInput k q n E) : ENNReal :=
  ∑ X : V × Fin n → ZMod q,
    ENNReal.ofReal (1 / (Fintype.card (V × Fin n → ZMod q) : ℝ)) *
      ∏ t, playerMass G Y α n (some X) (I t)

/-- The law of `(H_t, Z_t)_{t ∈ [T]}` in the NO case: the players' inputs are independent. -/
noncomputable def noMass (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n T : ℕ)
    (I : Fin T → PlayerInput k q n E) : ENNReal :=
  ∏ t, playerMass G Y α n none (I t)

/-- The public board: for each player so far, the hypergraph `H_t` (its count vector, written for
free) and the message. -/
abbrev Board (k n : ℕ) (E : Type) : Type :=
  List ((E × (Fin k → Fin n) → ℕ) × List Bool)

/-- **A deterministic `T`-player one-way blackboard protocol for DIHP** (§4.2, p.17).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.17: "The players speak one at a time
(t = 1, …, T). Each player writes an arbitrary function of their input (H_t, Z_t) and the previous board
contents (which counts for communication cost) on the blackboard, and is also allowed to write H_t
itself on the board for free."; "the final output is a function of the public transcript."

**Formalization Note.** Messages are bit strings of arbitrary length, and every `H_t` is on the board
for free, which only strengthens the protocol. Player `t` sees the board and its own input, not the
`Z`'s of other players. `output = true` is YES. -/
structure Protocol (k q n : ℕ) (E : Type) (T : ℕ) where
  /-- The message of player `t`, as a function of the board and the player's input. -/
  msg : Fin T → Board k n E → PlayerInput k q n E → List Bool
  /-- The output, as a function of the final board. -/
  output : Board k n E → Bool

namespace Protocol

variable {E' : Type} {T : ℕ}

/-- The final board on the inputs `I`, written in the order `t = 1, …, T`. -/
def transcript (P : Protocol k q n E' T) (I : Fin T → PlayerInput k q n E') : Board k n E' :=
  (List.finRange T).foldl (fun b t => b ++ [((I t).1, P.msg t b (I t))]) []

/-- The total number of message bits written on the inputs `I` (`H_t` is free). -/
def totalBits (P : Protocol k q n E' T) (I : Fin T → PlayerInput k q n E') : ℕ :=
  ((P.transcript I).map fun x => x.2.length).sum

/-- The communication cost is at most `b`: "the maximum total number of message bits written over
all inputs" (p.17). The maximum ranges over every input tuple, in or out of the support. -/
def CostLE (P : Protocol k q n E' T) (b : ℕ) : Prop :=
  ∀ I, P.totalBits I ≤ b

end Protocol

/-- The protocol's advantage `|P[output YES | YES case] − P[output YES | NO case]|` in the game
`DIHP_{Φ*}(α, T, n)` (Definition 4.3, p.17). -/
noncomputable def advantage (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n T : ℕ)
    (P : Protocol k q n E T) : ℝ :=
  |(∑' I, if P.output (P.transcript I) = true then yesMass G Y α n T I else 0).toReal -
    (∑' I, if P.output (P.transcript I) = true then noMass G Y α n T I else 0).toReal|

/-- `K_t`: the copies whose observed label is zero in all coordinates (§4.3, p.19). -/
def zeroCopies (I : PlayerInput k q n E) : Finset (Σ e, Fin (I.1 e)) :=
  Finset.univ.filter fun h => ∀ ℓ, I.2 (h, ℓ) = 0

/-- The probability that distinct `h_1, …, h_{m₁}` chosen uniformly at random from `K` lie over the
edges `e_1, …, e_{m₁}` of `G^n` (step 3 of the protocol, p.19): the fraction of injections
`[m₁] → K` that do. -/
noncomputable def selectProb {F : Type} [DecidableEq F] {c : F → ℕ} (K : Finset (Σ e, Fin (c e)))
    {m₁ : ℕ} (e : Fin m₁ → F) : ENNReal :=
  (Fintype.card {h : Fin m₁ ↪ K // ∀ i, (h i).1.1 = e i} : ENNReal) /
    (Fintype.card (Fin m₁ ↪ K) : ENNReal)

/-- `P[A_t = a_t for all t]`, where `A_t = |K_t|`. -/
noncomputable def countProb (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n T : ℕ)
    (lab : Option (V × Fin n → ZMod q)) (a : Fin T → ℕ) : ENNReal :=
  ∑' I : Fin T → PlayerInput k q n E,
    ∏ t, playerMass G Y α n lab (I t) * if (zeroCopies (I t)).card = a t then 1 else 0

/-- `P[A_t = a_t and player t's chosen copies lie over e_t(1), …, e_t(m₁), for all t]`. The players'
inputs and their public random choices are independent across `t` (p.20). -/
noncomputable def seqProb (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (α : ℝ) (n T m₁ : ℕ)
    (lab : Option (V × Fin n → ZMod q)) (a : Fin T → ℕ)
    (e : Fin T → Fin m₁ → E × (Fin k → Fin n)) : ENNReal :=
  ∑' I : Fin T → PlayerInput k q n E,
    ∏ t, playerMass G Y α n lab (I t) *
      (if (zeroCopies (I t)).card = a t then 1 else 0) * selectProb (zeroCopies (I t)) (e t)

/-- `p_e`: `p^YES_e(X) := 𝒴*(j)(X|_e)` for `lab = some X`, and `p^NO_e := q^{-k}` for `lab = none`
(p.19), for `e = (j, τ)` an edge of `G^n`. -/
noncomputable def zeroProb (G : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ) (n : ℕ)
    (lab : Option (V × Fin n → ZMod q)) (e : E × (Fin k → Fin n)) : ℝ :=
  match lab with
  | some X => Y e.1 (fun ℓ => X ((blowup G n).M e ℓ))
  | none => 1 / (q : ℝ) ^ k

end RandOrderCSP


