-- Prove2me | Definitions.Def_QaryCVP_corrAttempt
-- name    : QaryCVP_corrAttempt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:56.442093+00:00
-- url     : https://prove2.me/theorems/0a0310d0-e83e-4feb-aaf7-a9082fcb43dd
-- title:
--   One correction attempt $w=(\sigma v,u,e_j,0)$, its success probability and conditional mean
-- statement:
--   Let $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ and split its first $n_0+\ell+\ell'$ columns as $[A\ C_0\ C_1]$ with widths $n_0,\ell,\ell'$. For a right-hand side $s\in(\mathbb Z/q\mathbb Z)^m$, a **correction attempt** samples independent uniform $u\in\{0,1\}^\ell$, $j\in[\ell']$, $\sigma\in\{-1,1\}$, calls the short solver on
--
--   $$\big(A,\ \sigma(s-C_0u-C_1e_j)\big)$$
--
--   with its own independent randomness $\omega\sim\mu$, and on success $v$ returns $w=(\sigma v,u,e_j,0)\in\mathbb Z^n$. The same construction over an abstract finite abelian group $G$, with a homomorphism $A:\mathbb Z^{n_0}\to G$ and columns $C_0\in G^\ell$, $C_1\in G^{\ell'}$, returns $w=(\sigma v,u,e_j)$ (Lemma 4.4).
--
--   For a randomized procedure, $\Pr[\text{success}]$ is the probability that it returns a vector, and $\|\mathbb E[w\mid\text{success}]\|$ is the Euclidean norm of its unconditional mean output (failure counted as $0$) divided by $\Pr[\text{success}]$. For $r$ attempts, $\bar w(s)$ is the average of the successful outputs.
--
--   This is the step that turns average success over right-hand sides into success for every right-hand side.
--
--   **Formalization Note** Coordinates of the mean are integrals of bounded functions; every statement using them assumes bounded outputs and measurable outcome events. Indices are 0-based; a column index $\ge n$ reads as the zero column, which the correction branch never uses.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 3, lines 20–27, p.33; Lemma 4.4, p.36; Lemma 4.5, p.37; Lemma 4.6, p.38

import Mathlib
import Definitions.Def_QaryCVP_qaryLattice

open MeasureTheory ProbabilityTheory

namespace QaryCVP

/-- Column `k` (0-based) of `H`, or the zero column when `k ≥ n` (never reached on the
correction branch, where all used columns lie among the first `d ≤ n`). -/
def colOf {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (k : ℕ) : Fin m → ZMod q :=
  fun i => if h : k < n then H i ⟨k, h⟩ else 0

/-- The random choices of one correction attempt (Algorithm 3, line 22, p.33; Lemma 4.4, p.36):
`u ∈ {0,1}^ℓ`, `j ∈ [ℓ′]` (0-based), the sign `σ` (`true ↦ +1`, `false ↦ −1`) and the internal
randomness `ω` of the short solver. -/
abbrev AttSample (ℓ ℓ' : ℕ) (Ω : Type) := (Fin ℓ → Bool) × Fin ℓ' × Bool × Ω

/-- The law of one attempt's random choices: `u`, `j`, `σ` independent and uniform, and the
solver's randomness `ω ∼ μ`, independent of them (Lemma 4.4: "independent uniform u ∈ {0,1}^ℓ,
j ∈ [ℓ′], and σ ∈ {−1,1} … using independent internal randomness"). -/
noncomputable def attMeasure (ℓ ℓ' : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) :
    Measure (AttSample ℓ ℓ' Ω) :=
  (uniformOn (Set.univ : Set (Fin ℓ → Bool))).prod
    ((uniformOn (Set.univ : Set (Fin ℓ'))).prod ((uniformOn (Set.univ : Set Bool)).prod μ))

/-- One correction attempt on `H ∈ (Z/qZ)^{m×n}` for the right-hand side `s` (Algorithm 3,
lines 20–27, p.33; Lemma 4.5, p.37). The first `n₀ + ℓ + ℓ′` columns are split as `[A C₀ C₁]` with
widths `n₀, ℓ, ℓ′`; the attempt calls the short solver on `(A, σ(s − C₀u − C₁e_j))` and on success
`v` returns `w = (σv, u, e_j, 0)`.
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Algorithm 3, p.33.

**Formalization Note.** `Sq` is the short solver as a randomized function of `(A, t)` and its
randomness. -/
def corrAttempt {m n q : ℕ} {Ω : Type}
    (Sq : ∀ {n0 : ℕ}, Matrix (Fin m) (Fin n0) (ZMod q) → (Fin m → ZMod q) → Ω →
      Option (Fin n0 → ℤ))
    (H : Matrix (Fin m) (Fin n) (ZMod q)) (n0 ℓ ℓ' : ℕ) (s : Fin m → ZMod q)
    (a : AttSample ℓ ℓ' Ω) : Option (Fin n → ℤ) :=
  let u := a.1
  let j := a.2.1
  let σ := a.2.2.1
  let ω := a.2.2.2
  let sgnQ : ZMod q := if σ then 1 else -1
  let sgnZ : ℤ := if σ then 1 else -1
  let A : Matrix (Fin m) (Fin n0) (ZMod q) := fun i k => colOf H k.val i
  let C0u : Fin m → ZMod q := ∑ k : Fin ℓ, if u k then colOf H (n0 + k.val) else 0
  let C1ej : Fin m → ZMod q := colOf H (n0 + ℓ + j.val)
  let t : Fin m → ZMod q := sgnQ • (s - C0u - C1ej)
  (Sq A t ω).map fun v => fun i =>
    if h : i.val < n0 then sgnZ * v ⟨i.val, h⟩
    else if h' : i.val < n0 + ℓ then (if u ⟨i.val - n0, by omega⟩ then 1 else 0)
    else if i.val < n0 + ℓ + ℓ' then (if i.val = n0 + ℓ + j.val then 1 else 0)
    else 0

/-- Success probability of a randomized vector-valued procedure `X` under the law `ν`. -/
noncomputable def succProb {α : Type} [MeasurableSpace α] {k : Type} (ν : Measure α)
    (X : α → Option (k → ℤ)) : ℝ :=
  (ν {a | (X a).isSome}).toReal

/-- The norm `‖E[w | success]‖` of the conditional mean output of a randomized procedure `X`
(failure counted as `0` in the unconditional mean, which is then divided by the success
probability; Lemma 4.4, p.37).

**Formalization Note.** Coordinates are Bochner integrals of bounded functions; every statement
using it bounds the outputs and makes the outcome events measurable. -/
noncomputable def condMeanNorm {α : Type} [MeasurableSpace α] {k : Type} [Fintype k]
    (ν : Measure α) (X : α → Option (k → ℤ)) : ℝ :=
  Real.sqrt (∑ i, (∫ a, (((X a).getD 0) i : ℝ) ∂ν) ^ 2) / succProb ν X

/-- One attempt of Lemma 4.4 (p.36) over an abstract finite abelian group `G`: for the
homomorphism `A : Z^{n₀} → G`, columns `C₀ ∈ G^ℓ`, `C₁ ∈ G^{ℓ′}` and right-hand side `s`, call
`S(σ(s − C₀u − C₁e_j))` and on success `v` return `w = (σv, u, e_j)`, indexed by
`[n₀] ⊕ [ℓ] ⊕ [ℓ′]`. -/
def grpAttempt {G : Type} [AddCommGroup G] {n0 ℓ ℓ' : ℕ} {Ω : Type}
    (S : G → Ω → Option (Fin n0 → ℤ)) (C0 : Fin ℓ → G) (C1 : Fin ℓ' → G) (s : G)
    (a : AttSample ℓ ℓ' Ω) : Option (Fin n0 ⊕ (Fin ℓ ⊕ Fin ℓ') → ℤ) :=
  let u := a.1
  let j := a.2.1
  let σz : ℤ := if a.2.2.1 then 1 else -1
  let t : G := σz • (s - (∑ k : Fin ℓ, if u k then C0 k else 0) - C1 j)
  (S t a.2.2.2).map fun v => fun i =>
    match i with
    | Sum.inl k => σz * v k
    | Sum.inr (Sum.inl k) => if u k then 1 else 0
    | Sum.inr (Sum.inr k) => if k = j then 1 else 0

/-- Euclidean norm of a real vector. -/
noncomputable def eucNorm {k : Type} [Fintype k] (v : k → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- `w̄(s)`: the average of the successful outputs among `r` attempts `X (ωs i)` (Lemma 4.6,
p.38); the zero vector if none succeeds. -/
noncomputable def succAvg {α : Type} {k : Type} {r : ℕ} (X : α → Option (k → ℤ))
    (ωs : Fin r → α) : k → ℝ :=
  fun j => (∑ i ∈ Finset.univ.filter (fun i => (X (ωs i)).isSome), (((X (ωs i)).getD 0) j : ℝ)) /
    (Finset.univ.filter (fun i => (X (ωs i)).isSome)).card

end QaryCVP


