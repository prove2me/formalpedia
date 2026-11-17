-- Prove2me | Definitions.Def_FRouting_Supplement_UniformCTStrategy
-- name    : FRouting_Supplement_UniformCTStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:20:01.079404+00:00
-- url     : https://prove2.me/theorems/d426e7c1-a77f-40a3-8da9-6eb6b7846b99
-- title:
--   $(\mathcal T,t)$-uniform Clifford+T $f$-routing strategies on qubits
-- statement:
--   Let $\mathcal T,t:\mathbb N\to\mathbb N$. A **$(\mathcal T,t)$-uniform Clifford+T strategy** is a $\mathcal T$-uniform $f$-routing strategy on qubits (Definition 1.2 and Definition 3.6) whose resource-preparation channel $\mathcal I^n$ and pre-communication channels $\mathcal U^x$, $\mathcal V^y$ are Clifford+T circuits with at most $t(n)$ magic gates each, for every $n$ and all $x,y\in\{0,1\}^n$.
--
--   Concretely, three deterministic machines, one each for the resource, Alice and Bob, print on input $1^n$ (and $x$, respectively $y$) the descriptions of these circuits within $\max(1,\mathcal T(n))$ steps. Each circuit has size and width at most $\max(1,\mathcal T(n))$, the resource uses $q(n)\le\mathcal T(n)$ qubits per party, and the register layout is that of the base mission's uniform strategies: $L$ and $R$ for the resource, $QL\to A_1B_2$ for Alice and $R\to B_1A_2$ for Bob. The post-communication channels are arbitrary. At each length $n$ the family gives a routing strategy on qubits: the resource is the output state of the resource circuit on $|0^{2q}\rangle$, and Alice's and Bob's first channels are those of their printed circuits.
--
--   **Formalization Note** The construction of the routing strategy is the published `UniformStrategy.toRouting` at $d=2$, applied to the compiled circuits, so correctness is the published `IsCorrectOn`. The time budget is $\max(1,\mathcal T(n))$, as in the base mission, because a machine run takes at least one step.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 6.1, p.23; Definition 1.2, p.4; Definition 3.6, pp.15–16

import Definitions.Def_FRouting_UniformStrategy
import Definitions.Def_FRouting_Supplement_CTCircuit

set_option autoImplicit false

open Matrix

namespace FRouting.Supplement

open WildeQIT QAlgorithms.Complexity

/-- **A `(𝒯, t)`-uniform Clifford+T routing-strategy family on qubits.** Renard, *Computational Bounds
for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 6.1, p.23: "A 𝒯-uniform
f-routing strategy is a (𝒯, t)-uniform Clifford+T strategy if the resource generated channels ℐⁿ, 𝒰ˣ,
𝒱ʸ are all Clifford+T circuits with at most t(n) magic gates each, for every x, y ∈ {0,1}ⁿ", with
Definition 1.2 (p.4) and Definition 3.6 (pp.15–16) for 𝒯-uniform, at qudit dimension `d = 2`.

The data and clauses are those of the published `FRouting.UniformStrategy (fun _ => 2) 𝒯`, the circuits
being Clifford+T circuits printed in their description `encCTCircuit`:
- `genRes(1ⁿ)` prints the resource circuit, on `2q` wires, the first `q` being `L`, the last `q` `R`;
- `genA(1ⁿ, x)` prints `𝒰ˣ`: input wires `Q` (wire `0`) and `L`; output `A₁` (first `a₁` wires), `B₂`;
- `genB(1ⁿ, y)` prints `𝒱ʸ`: input wires `R`; output `B₁` (first `b₁` wires), `A₂`;
- each runs within the budget of `𝒯(n)`; each printed circuit has size and width at most that budget,
  `q ≤ 𝒯(n)`, and at most `t(n)` magic gates.

**Formalization Note** The post-communication channels are arbitrary, as in `UniformStrategy`
(`Gen^post` is unrestricted, p.16). The magic count bounds only `ℐⁿ, 𝒰ˣ, 𝒱ʸ`, as Definition 6.1 says.
`t` carries no hypothesis. -/
structure UniformCTStrategy (T t : ℕ → ℕ) where
  /-- The machine `Gen_res`. -/
  genRes : StrMachine
  /-- The machine `Gen^pre_A`. -/
  genA : StrMachine
  /-- The machine `Gen^pre_B`. -/
  genB : StrMachine
  /-- The number `q(n)` of qubits per adversary of the resource. -/
  q : ℕ → ℕ
  /-- The resource circuit `ℐⁿ_{LR→LR}`. -/
  res : ∀ n, CTCircuit (q n + q n) (q n + q n)
  /-- The width of `A₁`. -/
  a₁ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `B₂`. -/
  b₂ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `B₁`. -/
  b₁ : ∀ n, (Fin n → Bool) → ℕ
  /-- The width of `A₂`. -/
  a₂ : ∀ n, (Fin n → Bool) → ℕ
  /-- The circuit of `𝒰ˣ_{QL→A₁B₂}`. -/
  preA : ∀ n x, CTCircuit (q n + 1) (a₁ n x + b₂ n x)
  /-- The circuit of `𝒱ʸ_{R→B₁A₂}`. -/
  preB : ∀ n y, CTCircuit (q n) (b₁ n y + a₂ n y)
  /-- The channel `𝒰ˣʸᵇ_{A₁A₂→Q₀}`. -/
  decA : ∀ n x y, Bool → QChannel (quditReg 2 (a₁ n x) × quditReg 2 (a₂ n y)) (Fin 2)
  /-- The channel `𝒱ˣʸᵇ_{B₁B₂→Q₁}`. -/
  decB : ∀ n x y, Bool → QChannel (quditReg 2 (b₁ n y) × quditReg 2 (b₂ n x)) (Fin 2)
  res_prints : ∀ n, PrintsInTime genRes (List.replicate n true) (encCTCircuit (res n)) (budget T n)
  preA_prints : ∀ n x, PrintsInTime genA (encNat n ++ List.ofFn x)
    (encNat (a₁ n x) ++ encNat (b₂ n x) ++ encCTCircuit (preA n x)) (budget T n)
  preB_prints : ∀ n y, PrintsInTime genB (encNat n ++ List.ofFn y)
    (encNat (b₁ n y) ++ encNat (a₂ n y) ++ encCTCircuit (preB n y)) (budget T n)
  q_le : ∀ n, q n ≤ T n
  res_size : ∀ n, (res n).size ≤ budget T n ∧ (res n).width ≤ budget T n
  preA_size : ∀ n x, (preA n x).size ≤ budget T n ∧ (preA n x).width ≤ budget T n
  preB_size : ∀ n y, (preB n y).size ≤ budget T n ∧ (preB n y).width ≤ budget T n
  res_magic : ∀ n, (res n).magicCount ≤ t n
  preA_magic : ∀ n x, (preA n x).magicCount ≤ t n
  preB_magic : ∀ n y, (preB n y).magicCount ≤ t n

namespace UniformCTStrategy

variable {T t : ℕ → ℕ} (S : UniformCTStrategy T t)

/-- **The strategy at length `n`**, built exactly as the published `UniformStrategy.toRouting`: the
channels of the printed circuits, and the resource `ℐⁿ(|0^{2q}⟩⟨0^{2q}|)` (p.16, step 1). -/
noncomputable def toRouting (n : ℕ) : RoutingStrategy n 2 where
  L := quditReg 2 (S.q n)
  R := quditReg 2 (S.q n)
  A₁ x := quditReg 2 (S.a₁ n x)
  B₂ x := quditReg 2 (S.b₂ n x)
  B₁ y := quditReg 2 (S.b₁ n y)
  A₂ y := quditReg 2 (S.a₂ n y)
  resource :=
    let e : (quditReg 2 (S.q n) × quditReg 2 (S.q n)) ≃ (Fin (S.q n + S.q n) → Fin 2) :=
      Fin.appendEquiv (S.q n) (S.q n)
    ((S.res n).toCircuit.outputState).submatrix e e
  resource_density :=
    isDensity_submatrix _ (QChannel_apply_isDensity _ (single_zero_isDensity _))
  U x := chanReindex
    (Fin.consEquiv fun _ => Fin 2).symm
    (Fin.appendEquiv (S.a₁ n x) (S.b₂ n x)).symm (S.preA n x).toCircuit.channel
  V y := chanReindex (Equiv.refl _)
    (Fin.appendEquiv (S.b₁ n y) (S.a₂ n y)).symm (S.preB n y).toCircuit.channel
  Uₚ x y b := S.decA n x y b
  Vₚ x y b := S.decB n x y b

end UniformCTStrategy

end FRouting.Supplement


