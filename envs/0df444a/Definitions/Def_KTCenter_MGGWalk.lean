-- Prove2me | Definitions.Def_KTCenter_MGGWalk
-- name    : KTCenter_MGGWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:50.01189+00:00
-- url     : https://prove2.me/theorems/91d0d415-be21-4bb4-9f2e-5dde920d0b71
-- title:
--   Margulis–Gabber–Galil walks on $\mathbb Z_m\times\mathbb Z_m$ and the map $\psi_B$
-- statement:
--   For $m\ge2$, the Margulis–Gabber–Galil multigraph on $H=m^2$ states $\mathbb Z_m\times\mathbb Z_m$ is eight-regular: with $T_1(x,y)=(x+2y,y)$ and $T_2(x,y)=(x,y+2x)$, the state $s$ steps to $T_1s$, $T_2s$, $T_1s+e_1$, $T_2s+e_2$ or to one of their four inverses. Its normalized transition operator is $Pf(s)=\frac18\sum_{l=1}^8 f(\text{step}_l(s))$. A **walk visiting $T$ states** is described by an initial state and $T-1$ labels, $H\cdot 8^{T-1}$ descriptions in all (83); the expectation over a uniformly started walk is the uniform average over the descriptions. The map $\psi_B$ (85) sends a state index $z\in\{0,\dots,H-1\}$ to the candidate at index $1+\lfloor |B|z/H\rfloor$ of $B$.
--
--   These walks replace independent samples in the derandomization (§6.2).
--
--   **Formalization Note** The paper does not print the graph; it cites Hoory–Linial–Wigderson, *Expander graphs and their applications* (Bull. AMS 2006), Construction 8.1. The formula here is that construction as recalled, not checked against the survey. The candidates of $B$ are taken in increasing order and the state $(x,y)$ has index $xm+y$; both are orderings the paper leaves free.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §6.2.1, eqs. (83), (85), p.61 (PDF p.63); graph from [HLW06, Construction 8.1]

import Mathlib

namespace KTCenter

/-- **The Margulis–Gabber–Galil transitions on `ℤ_m × ℤ_m`**, §6.2.1, p.61 (PDF p.63), which cites
[HLW06, Construction 8.1].

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** The paper does not print this formula. It is Hoory, Linial, Wigderson,
*Expander graphs and their applications* (Bull. AMS 2006), Construction 8.1, written from memory
of that survey and not checked against it, since no platform session may fetch it: with
`T₁(x, y) = (x + 2y, y)`, `T₂(x, y) = (x, y + 2x)`, labels `0, …, 3` are `T₁v`, `T₂v`, `T₁v + e₁`,
`T₂v + e₂` and labels `4, …, 7` are their inverses. The label order is a convention. -/
def mggStep (m : ℕ) (l : Fin 8) (s : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (![(s.1 + 2 * s.2, s.2), (s.1, s.2 + 2 * s.1),
     (s.1 + 2 * s.2 + 1, s.2), (s.1, s.2 + 2 * s.1 + 1),
     (s.1 - 2 * s.2, s.2), (s.1, s.2 - 2 * s.1),
     (s.1 - 2 * s.2 - 1, s.2), (s.1, s.2 - 2 * s.1 - 1)] : Fin 8 → ZMod m × ZMod m) l

/-- **The normalized transition matrix** `P`, as an operator on functions, p.61. -/
noncomputable def mggP (m : ℕ) (f : ZMod m × ZMod m → ℝ) (s : ZMod m × ZMod m) : ℝ :=
  (1 / 8 : ℝ) * ∑ l : Fin 8, f (mggStep m l s)

/-- **The states of a walk visiting `T` states**, p.61: the initial state `z`, and `T − 1` labels
`ls`. `walkState m T z ls j` is the source's `X_{j+1}` for `j < T`. -/
def walkState (m T : ℕ) (z : ZMod m × ZMod m) (ls : Fin (T - 1) → Fin 8) :
    ℕ → ZMod m × ZMod m
  | 0 => z
  | j + 1 =>
    if h : j < T - 1 then mggStep m (ls ⟨j, h⟩) (walkState m T z ls j)
    else walkState m T z ls j

/-- **The expectation over a uniformly started walk**, p.61: the uniform average over the
`H · 8^{T−1}` walk descriptions of (83), `H = m²`. A finite sum. -/
noncomputable def walkAvg (m T : ℕ) [NeZero m] (G : (ℕ → ZMod m × ZMod m) → ℝ) : ℝ :=
  (1 / ((m : ℝ) ^ 2 * 8 ^ (T - 1))) *
    ∑ z : ZMod m × ZMod m, ∑ ls : Fin (T - 1) → Fin 8, G (walkState m T z ls)

/-- The identification of the `H = m²` states with `0, …, H − 1`, p.61. -/
def stateIndex (m : ℕ) (s : ZMod m × ZMod m) : ℕ := s.1.val * m + s.2.val

/-- `ψ_B(z)`, eq. (85), p.61, as a lookup: `Option` value of "the candidate at index
`1 + ⌊|B|z/H⌋` in `B`", with the candidates of `B` in increasing order, 0-based here. The value is
`some` for `z < H`. -/
def psiLookup {N : ℕ} (B : Finset (Fin N)) (H z : ℕ) : Option (Fin N) :=
  (B.sort (· ≤ ·))[B.card * z / H]?

end KTCenter


