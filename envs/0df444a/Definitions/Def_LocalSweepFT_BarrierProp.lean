-- Prove2me | Definitions.Def_LocalSweepFT_BarrierProp
-- name    : LocalSweepFT_BarrierProp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:41:36.513232+00:00
-- url     : https://prove2.me/theorems/691ede25-80da-4d62-8828-ff642bd96204
-- title:
--   Small fillings, the filling class $[x]$ and the barrier property
-- statement:
--   Let $x$ be a $d'$-chain of the torus $\mathcal T^d_n$. A **small filling** of $x$ is a chain $y=\sum_\kappa y_\kappa$, the sum over the connected components $\kappa$ of $\partial^-x$, with $\partial^-y_\kappa=\kappa$ and $\mathrm{Size}(y_\kappa)\le\mathrm{Size}(\kappa)$. The filling class of $x$ is **trivial**, $[x]=[0]$, if $x$ has a small filling and $x+y\in\operatorname{im}\partial^-$ (an X-stabilizer) for every small filling $y$.
--
--   The **barrier property** with step bound $\Delta$ and constant $c'$ says: for every sequence $x_1,\dots,x_{t+1}$ of $d'$-chains with $x_1\in\operatorname{im}\partial^-$, consecutive chains at Hamming distance at most $\Delta$, and every connected component of every $\partial^-x_i$ of size at most $c'n$, every $x_i$ has trivial filling class:
--   $$[0]=[x_1]=[x_2]=\dots=[x_{t+1}].$$
--
--   This is the statement of Claims 5.9 and 5.10: a logical error forces an intermediate syndrome cluster of linear size.
--
--   **Formalization Note** Def. 5.7 fixes one canonical reduced filling per component; triviality is required for every small filling, which is at least as strong.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.6, p.41; Definition 5.7, pp.41–42; Claims 5.9–5.10, pp.42–43

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): fillings and the filling operator `[x]` (Claim 5.6, p.41;
Definition 5.7, pp.41–42), and the barrier property of Claims 5.9–5.10 (pp.42–43). -/

variable {d d' : ℕ}

/-- `y` is a small filling of the torus chain `x ∈ C_{d′}(T^d_n)`: `y = Σ_κ y_κ` over the connected
components `κ` of `∂⁻x`, where `∂⁻y_κ = κ` and `Size(y_κ) ≤ Size(κ)` (the fillings of Claim 5.6,
p.41, used in Def 5.7). -/
def IsSmallFilling (n : ℕ) (x y : Chain (ZMod n) d d') : Prop :=
  ∃ f : Chain (ZMod n) d (d' - 1) → Chain (ZMod n) d d',
    (∀ κ ∈ components (bdry x), bdry (f κ) = κ ∧ sizeT n (f κ) ≤ sizeT n κ) ∧
    y = ∑ κ ∈ components (bdry x), f κ

/-- `[x] = [0]` (Def 5.7, pp.41–42): `x` has a small filling, and for every small filling `y` the
cycle `x + y` is an X-stabilizer (lies in `im ∂⁻ : C_{d′+1} → C_{d′}`), i.e. its homology class
(logical operator) is trivial.

**Formalization Note.** Def 5.7 fixes one canonical filling per component; the class is required to
vanish for every admissible choice of fillings, which is at least as strong. -/
def HasTrivialClass (n : ℕ) (x : Chain (ZMod n) d d') : Prop :=
  (∃ y, IsSmallFilling n x y) ∧ ∀ y, IsSmallFilling n x y → x + y ∈ bdryRange (ZMod n) d d'

/-- The barrier property with step bound `Δ` and size constant `c′` on `T^d_n` (Claims 5.9–5.10,
pp.42–43): for every sequence `x_1, …, x_{t+1}` of `d′`-chains with `x_1` trivial (an
X-stabilizer), consecutive chains at Hamming distance `≤ Δ`, and every connected component of every
`∂⁻x_i` of size `≤ c′n`, every `x_i` has trivial filling class: `[0] = [x_1] = … = [x_{t+1}]`. -/
def BarrierProp (d d' n Δ : ℕ) (c' : ℝ) : Prop :=
  ∀ (t : ℕ) (x : Fin (t + 1) → Chain (ZMod n) d d'),
    x 0 ∈ bdryRange (ZMod n) d d' →
    (∀ i : Fin t, hamming (x i.castSucc) (x i.succ) ≤ Δ) →
    (∀ i, ∀ κ ∈ components (bdry (x i)), (sizeT n κ : ℝ) ≤ c' * n) →
    ∀ i, HasTrivialClass n (x i)

end LocalSweepFT


