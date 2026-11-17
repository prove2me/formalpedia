-- Prove2me | Definitions.Def_ImpuritySim_Supplement_ThermalMachine
-- name    : ImpuritySim_Supplement_ThermalMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:31:56.903564+00:00
-- url     : https://prove2.me/theorems/fc1cce8f-05d5-4294-ae8d-c565f99bcc40
-- title:
--   Gaussian observables $\alpha\exp(\frac14\sum A_{jk}\gamma_j\gamma_k)$ and the randomized real-RAM input of Theorem 6.8
-- statement:
--   A **Gaussian observable** (Definition 6.7) on $n$ fermionic modes is an operator
--   $$O=\alpha\exp\Bigl(\frac14\sum_{j,k=1}^{2n}A_{jk}\gamma_j\gamma_k\Bigr)$$
--   for a scalar $\alpha\in\mathbb C$ and an antisymmetric $2n\times2n$ matrix $A$, where $\gamma_1,\dots,\gamma_{2n}$ are the Majorana operators.
--
--   For Theorem 6.8 the algorithm runs on the published unit-cost real RAM with fair coins (the machine of the mission's goal). Its input is: integer memory $I_0=n$, $I_1=m$; real memory $M_0=\beta$, $M_1=\epsilon$, $M_2=J$, $M_3=\alpha$ (the energy shift of (1.1)), $M_4=\operatorname{Re}\alpha_O$, $M_5=\operatorname{Im}\alpha_O$, then $h$, $\operatorname{Re}A$, $\operatorname{Im}A$ row by row in three consecutive blocks of $4n^2$ cells, then the impurity coefficients $c_A$ at $6+12n^2+\sum_{a\in A}2^a$. The estimate $\hat Z$ is read from memory cell $M_{-1}$ after the machine halts; $\hat\mu$ is its output. A program **makes no query** if it contains no oracle instruction (coin flips are allowed).
--
--   **Formalization Note** Majoranas are the published 0-based Jordan–Wigner generators; the input cells are pairwise distinct.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Definition 6.7 and Theorem 6.8, p.34; model (1.1), p.4; (2.12), p.12

import Mathlib
import Definitions.Def_ImpuritySim_Model
import Definitions.Def_ImpuritySim_Machine

namespace ImpuritySim.Supplement

/-!
# Gaussian observables (Definition 6.7) and the randomized real RAM of Theorem 6.8

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2):
Definition 6.7 and Theorem 6.8, p.34; model (1.1), p.4; (2.12), p.12.

**Formalization Note.**
* `gaussObs n αO A = α exp(¼ Σ_{j,k} A_{jk} γ_j γ_k)` (Definition 6.7), both indices over all `2n`
  Majoranas (the published 0-based `gamma n`), with a complex scalar `α` and a complex
  `2n × 2n` matrix `A`; antisymmetry `Aᵀ = −A` is a hypothesis where it is used. `exp` is the matrix
  exponential `NormedSpace.exp`.
* The machine is the published `SubsetConvFPRAS` unit-cost real RAM, the machine of the published
  goal (Theorem 5.3), now with its fair coins. `NoQuery P`: `P` has no `query` instruction (`coin`
  is allowed). Probabilities are by counting coin strings `Fin B → Bool` (`SubsetConvFPRAS.tapeCount`):
  an event has probability `≥ 2/3` after `B` steps iff `3 · tapeCount ≥ 2 · 2^B`.
* Input (`start68`): integer memory `I 0 = n`, `I 1 = m`, `0` elsewhere; real memory
  `M 0 = β`, `M 1 = ϵ`, `M 2 = J`, `M 3 = α` (energy shift of (1.1)), `M 4 = Re α_O`, `M 5 = Im α_O`,
  `M (6 + 2n·j + k) = h_{jk}`, `M (6 + 4n² + 2n·j + k) = Re A_{jk}`, `M (6 + 8n² + 2n·j + k) = Im A_{jk}`
  (`j, k : Fin (2n)`, 0-based), `M (6 + 12n² + Σ_{a ∈ A} 2^a) = c_A` for every even `A ⊆ Fin (2m)`,
  and `0` elsewhere. These cells are pairwise distinct (the four blocks occupy the disjoint ranges
  `[6, 6+4n²)`, `[6+4n², 6+8n²)`, `[6+8n², 6+12n²)`, `[6+12n², 6+12n²+2^{2m})`).
* Output: `μ̂` is the output register (`halt`), `Ẑ` is real-memory cell `M (−1)` of the final state
  (no input cell is negative). After `halt` the state stutters, so both are final.
-/

open FermiCap.Gaussian

/-- A Gaussian observable `O = α exp(¼ Σ_{j,k} A_{jk} γ_j γ_k)` (Definition 6.7). -/
noncomputable def gaussObs (n : ℕ) (αO : ℂ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Op n :=
  αO • NormedSpace.exp ((1 / 4 : ℂ) • ∑ j, ∑ k, A j k • (gamma n j * gamma n k))

/-- No oracle: the program contains no `query` instruction (coins are allowed). -/
def NoQuery (P : SubsetConvFPRAS.Program) : Prop :=
  ∀ op ∈ P, ∀ (which : Bool) (d bank : ℕ), op ≠ SubsetConvFPRAS.Instr.query which d bank

/-- Real input of Theorem 6.8: `β, ϵ, J, α, Re α_O, Im α_O`, then `h`, `Re A`, `Im A` row by row,
then the impurity coefficients `c_A`. -/
noncomputable def encodeReals68 (n m : ℕ) (β ϵ J α : ℝ) (αO : ℂ)
    (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (c : Finset (Fin (2 * m)) → ℝ) : ℤ → ℝ := fun z =>
  if z = 0 then β else if z = 1 then ϵ else if z = 2 then J else if z = 3 then α
  else if z = 4 then αO.re else if z = 5 then αO.im else
    (∑ j : Fin (2 * n), ∑ k : Fin (2 * n),
        ((if z = (6 + 2 * n * j.val + k.val : ℕ) then h j k else 0) +
          (if z = (6 + 4 * n ^ 2 + 2 * n * j.val + k.val : ℕ) then (A j k).re else 0) +
          (if z = (6 + 8 * n ^ 2 + 2 * n * j.val + k.val : ℕ) then (A j k).im else 0))) +
      ∑ B : Finset (Fin (2 * m)),
        if Even B.card ∧ z = (6 + 12 * n ^ 2 + ∑ a ∈ B, 2 ^ a.val : ℕ) then c B else 0

/-- The initial state of Theorem 6.8 on input `(n, m, β, ϵ, J, α, α_O, h, A, c)`. -/
noncomputable def start68 (n m : ℕ) (β ϵ J α : ℝ) (αO : ℂ)
    (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (c : Finset (Fin (2 * m)) → ℝ) : SubsetConvFPRAS.State 0 :=
  SubsetConvFPRAS.mkInit (encodeInts n m) (fun _ => ∅) (encodeReals68 n m β ϵ J α αO h A c)

/-- The second output `Ẑ` of a state: real-memory cell `−1`. -/
def zHat (s : SubsetConvFPRAS.State 0) : ℝ := s.core.mem (-1)

end ImpuritySim.Supplement


