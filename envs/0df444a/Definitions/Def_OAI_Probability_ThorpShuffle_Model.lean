-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Model
-- name    : OAI_Probability_ThorpShuffle_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:18:20.021055+00:00
-- url     : https://prove2.me/theorems/d3459717-c06f-4f4f-a606-a9535cea01f9
-- title:
--   The Thorp shuffle on $2^d$ cards: positions, coin vectors, one shuffle step and runs
-- statement:
--   This module sets up the Thorp shuffle of a deck of $2^d$ cards in binary coordinates. Booleans are identified with bits (false $=0$, true $=1$), $\oplus$ denotes addition modulo $2$, and $Q_d=\{0,1\}^d$ is the set of positions; a position is a bit string $x=(x_0,x_1,\dots,x_{d-1})$.
--
--   1. *States.* A state of the deck is a permutation of the positions, so the set of states is the symmetric group $\mathrm{Sym}(Q_d)$.
--   2. *Coin vectors.* For $d\ge 1$ a coin vector is a function $c:Q_{d-1}\to\{0,1\}$, one coin for each of the $2^{d-1}$ pairs of positions that agree in their last $d-1$ bits. For $d=0$ there is exactly one (trivial) coin vector.
--   3. *Pair switch.* For $c:Q_d\to\{0,1\}$, the involution of $\{0,1\}\times Q_d$ given by $(b,s)\mapsto(b\oplus c(s),\,s)$. It exchanges $(0,s)$ and $(1,s)$ exactly when $c(s)=1$.
--   4. *Rotation.* The permutation $R_d$ of $Q_d$ that shifts coordinates cyclically, $(R_dx)_i=x_{i+1 \bmod d}$, that is, $R_d(x_0,x_1,\dots,x_{d-1})=(x_1,\dots,x_{d-1},x_0)$.
--   5. *One shuffle step.* For $d\ge 1$ and a coin vector $c:Q_{d-1}\to\{0,1\}$, the step $T_c\in\mathrm{Sym}(Q_d)$ splits off the leading bit, applies the pair switch and then rotates:
--   $$
--   T_c(x_0,x_1,\dots,x_{d-1})=\bigl(x_1,\dots,x_{d-1},\;x_0\oplus c(x_1,\dots,x_{d-1})\bigr).
--   $$
--   For $d=0$ the step is the identity.
--   6. *Histories and runs.* A history of length $t$ is a sequence $\omega=(\omega_0,\dots,\omega_{t-1})$ of coin vectors. Its run is the composite permutation
--   $$
--   \mathrm{run}_t(\omega)=T_{\omega_{t-1}}\circ\cdots\circ T_{\omega_1}\circ T_{\omega_0}\in\mathrm{Sym}(Q_d),
--   $$
--   so the step with coins $\omega_0$ is applied first, and the empty history gives the identity.
--
--   Read $x$ as the binary expansion of a card position with $x_0$ the most significant bit. Then $x_0$ says which half of the deck the card is in, and the two positions that differ only in $x_0$ hold the $k$-th card of each half. A step orders each such pair by its own coin and interleaves the pairs, so the pair with tail $s=(x_1,\dots,x_{d-1})$ lands in the consecutive positions $(s,0)$ and $(s,1)$. With independent uniformly random coin vectors, $\mathrm{run}_t$ is the Thorp shuffle viewed as a random walk on $\mathrm{Sym}(Q_d)$. All later modules of this development are built on these objects.
--
--   **Formalization Note** `Position d` is `Fin d → Bool` (from the base definitions), `State d` is `Equiv.Perm (Position d)`, and `Coins` is defined by recursion: `Unit` at `0` and `Position d → Bool` at `d + 1`, with `Fintype` and `Inhabited` instances. `rotate` is `Equiv.piCongrLeft` along `(finRotate d).symm`. `step` is assembled from `Fin.consEquiv`, `pairSwitch` and `rotate`. `run` is the product of the reversed list of steps in `Equiv.Perm`, where the product $gh$ means $g\circ h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal

namespace OAI

universe u v

noncomputable section
open scoped BigOperators
open Filter

namespace Thorp

abbrev State (d : ℕ) := Equiv.Perm (Position d)

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Position d → Bool

instance coinsFintype (d : ℕ) : Fintype (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

instance coinsInhabited (d : ℕ) : Inhabited (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

def pairSwitch (d : ℕ) (c : Position d → Bool) : Equiv.Perm (Bool × Position d) where
  toFun p := (p.1 ^^ c p.2, p.2)
  invFun p := (p.1 ^^ c p.2, p.2)
  left_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]
  right_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]

def rotate (d : ℕ) : State d :=
  Equiv.piCongrLeft (fun _ : Fin d => Bool) (finRotate d).symm

def step : (d : ℕ) → Coins d → State d
  | 0, _ => Equiv.refl _
  | d + 1, c =>
    (((Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm.trans
      (pairSwitch d c)).trans
      (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))).trans (rotate (d + 1))

abbrev History (d t : ℕ) := Fin t → Coins d

def run (d t : ℕ) (ω : History d t) : State d :=
  ((List.ofFn fun i : Fin t => step d (ω i)).reverse).prod

end Thorp

end

end OAI


