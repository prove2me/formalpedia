-- Prove2me | Definitions.Def_ApproxGKR_Instance
-- name    : ApproxGKR_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:16.042147+00:00
-- url     : https://prove2.me/theorems/c5fe75bc-2514-4fc7-881c-5157cf48da8f
-- title:
--   Instances, encodings, oracle validity, honest transcripts and acceptance probability
-- statement:
--   The interface between the protocol of Theorem C.1 and the machine.
--   1. **Public parameters** $(L,(m_i)_{i\le L},t,\delta,B_V,B_W,\Delta,\varepsilon)$ and the **instance** (parameters, claim $y$, input list), with a self-delimiting binary encoding; $b_{\mathrm{in}}$ is the largest bit size of $y,\Delta,\varepsilon$ and the input values, and $\beta=b_{\mathrm{in}}+L+k+D+mh+\mathrm{size}(B_V)+\mathrm{size}(B_W)$.
--   2. The circuit's gate list (the honest prover's knowledge) and the honest prover's input for message $t$: circuit, instance, $t$ and the coins sent before $t$.
--   3. **Valid oracle answers**: every well-formed query (layer $i<L$, point with $k_i$ coordinates) is answered within the requested error $2^{-p}$ of the exact value of $\widetilde{\mathrm{add}}_i$ or $\widetilde{\mathrm{mult}}_i$ at the root point ("both parties may query these polynomials at tuples of roots of unity to any requested absolute error", p.30).
--   4. Coin tuples in $(\mathbb Z/2^\ell)^R$, acceptance of a verifier program, honest transcripts, and the **acceptance probability** against a deterministic adaptive prover $P^*$ (message $t$ a function of the earlier coins) over the uniform coin tuple.
--   5. The query discipline: every query is for a layer $i<L$, and at most one query of each type per layer.
--   6. Two's-complement output bits (for Lemma D.6).
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), Theorem C.1, pp.33–34; App. B.2, p.27; §C.1, pp.30, 32

import Mathlib
import Definitions.Def_ApproxGKR_LayeredCircuit
import Definitions.Def_ApproxGKR_RAMRun

namespace ApproxGKR

/-! The interface of the protocol of Theorem C.1 with the machine: instance and circuit
encodings, the public parameters, bit sizes, oracle validity, coin tuples, honest transcripts,
acceptance probability and the oracle-query discipline. -/

/-- Self-delimiting binary encoding of a natural number: each bit (least significant first) is
preceded by `true`, and `false` ends the number. -/
def encNat (n : ℕ) : List Bool := (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Encoding of a list of naturals (concatenation of the self-delimiting codes). -/
def encNats (l : List ℕ) : List Bool := l.flatMap encNat

/-- An integer as (sign bit, modulus). -/
def intCode (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

/-- A Gaussian dyadic `(A, B, p)` as naturals. -/
def dyadicCode (z : GaussDyadic) : List ℕ := intCode z.1 ++ intCode z.2.1 ++ [z.2.2]

/-- A rational as (numerator, denominator). -/
def ratCode (q : ℚ) : List ℕ := intCode q.num ++ [q.den]

/-- The **public parameters** known to both parties, other than `y` and the input: the depth `L`,
the list `m₀, …, m_L`, `t` with `h = 2^t`, the degree bound `δ`, the integers `B_V, B_W`, and the
rationals `∆, ε` (Theorem C.1, p.33: "`B_V, B_W ≥ 1` be integers, known to both parties", p.32). -/
structure Params where
  L : ℕ
  m : List ℕ
  t : ℕ
  δ : ℕ
  BV : ℕ
  BW : ℕ
  Δ : ℚ
  ε : ℚ

namespace Params

variable (p : Params)

/-- `m_i` read from the list. -/
def mAt (i : ℕ) : ℕ := p.m.getD i 0
/-- `h = 2^t`. -/
def h : ℕ := 2 ^ p.t
/-- `k_i = m_i + 2m_{i+1}`. -/
def ki (i : ℕ) : ℕ := p.mAt i + p.mAt (i + 1) + p.mAt (i + 1)
/-- `k = Σ_{i<L} k_i`. -/
def k : ℕ := ∑ i ∈ Finset.range p.L, p.ki i
/-- `m = max_{i ≤ L} m_i`. -/
def mMax : ℕ := (Finset.range (p.L + 1)).sup p.mAt
/-- `D = δ + h − 1`. -/
def D : ℕ := p.δ + p.h - 1

end Params

/-- The verifier's **instance**: the public parameters, the claimed output `y = (A + iB)2^{−p}`
and the input list. -/
structure Instance where
  params : Params
  y : GaussDyadic
  inputs : InputList

/-- The instance as a list of naturals. -/
def Instance.code (q : Instance) : List ℕ :=
  [q.params.L, q.params.m.length] ++ q.params.m ++
    [q.params.t, q.params.δ, q.params.BV, q.params.BW] ++
    ratCode q.params.Δ ++ ratCode q.params.ε ++ dyadicCode q.y ++ [q.inputs.length] ++
    q.inputs.flatMap (fun e => [e.1.length] ++ e.1 ++ dyadicCode e.2)

/-- The instance as a bit string. -/
def Instance.encode (q : Instance) : List Bool := encNats q.code

/-- The instance of a circuit `C`, degree bound `δ`, bounds `B_V, B_W`, thresholds `∆, ε`, claim
`y` and input list `x`. -/
def mkInstance (C : LayeredCircuit) (δ BV BW : ℕ) (Δ ε : ℚ) (y : GaussDyadic)
    (x : InputList) : Instance :=
  ⟨⟨C.L, (List.range (C.L + 1)).map C.m, C.t, δ, BV, BW, Δ, ε⟩, y, x⟩

/-- `b_in`: the largest bit size among the numbers of the instance (`y`, `∆`, `ε` and the input
values). -/
def binSize (q : Instance) : ℕ :=
  max (dsize q.y) (max (qsize q.params.Δ) (max (qsize q.params.ε)
    ((q.inputs.map (fun e => dsize e.2)).foldr max 0)))

/-- `β = b_in + L + k + D + m·h + size(B_V) + size(B_W)`: the scale in which the working bit
length `b` must be polynomial (decision 5 of the plan; the paper's analysis on pp.35, 40). -/
def betaSize (q : Instance) : ℕ :=
  binSize q + q.params.L + q.params.k + q.params.D + q.params.mMax * q.params.h +
    Nat.size q.params.BV + Nat.size q.params.BW

/-- The index `Σ_j g_j h^j` of a label. -/
def labelIndex {h m : ℕ} (g : Fin m → Fin h) : ℕ := ∑ j, (g j : ℕ) * h ^ (j : ℕ)

/-- The label of layer `i` with a given index. -/
def labelOfIndex (C : LayeredCircuit) (i idx : ℕ) : C.Label i :=
  fun j => ⟨idx / C.h ^ (j : ℕ) % C.h, Nat.mod_lt _ (pow_pos (by norm_num) _)⟩

/-- The circuit's gate list, layer by layer and label by label: type (`0` add, `1` mult) and the
indices of the two children. This is the honest prover's knowledge of the circuit. -/
def circuitCode (C : LayeredCircuit) : List ℕ :=
  (List.range C.L).flatMap fun i =>
    (List.range (C.h ^ C.m i)).flatMap fun idx =>
      [if (C.gate i (labelOfIndex C i idx)).1 = GateType.add then 0 else 1,
        labelIndex (C.gate i (labelOfIndex C i idx)).2.1,
        labelIndex (C.gate i (labelOfIndex C i idx)).2.2]

/-- The honest prover's input for message `t`: the circuit, the instance, `t` and the coins
`c₁, …, c_{t−1}` sent so far. -/
def proverInput (C : LayeredCircuit) (q : Instance) (t : ℕ) (coins : List ℕ) : List Bool :=
  encNats ([(circuitCode C).length] ++ circuitCode C ++ q.code ++ [t, coins.length] ++ coins)

/-- The gate type of a query. -/
def queryType (q : Query) : GateType := if q.type = 0 then GateType.add else GateType.mult

/-- **Valid oracle answers** for the extensions `ext`: every well-formed query (a layer `i < L`
and a point with `kᵢ` coordinates) is answered within the requested error `2^{−p}` of the exact
value of `add~ᵢ` or `mult~ᵢ` at the point of roots `exp(2πi aⱼ/2^{logN})`. Malformed queries may
be answered arbitrarily. ("both parties may query these polynomials at tuples of roots of unity to
any requested absolute error", p.30.) -/
def OracleValid (C : LayeredCircuit) (ext : ExtFamily C) (O : OracleAnswers) : Prop :=
  ∀ q : Query, q.layer < C.L → q.point.length = C.ki q.layer →
    ‖dyadicVal ((O q).1, (O q).2, q.prec) -
        MvPolynomial.eval (fun v : Fin (C.ki q.layer) => root (2 ^ q.logN) (q.point.getD v 0))
          (ext q.layer (queryType q))‖ ≤ (2 : ℝ) ^ (-(q.prec : ℤ))

/-- The coin `t` (`1 ≤ t ≤ R`) of a coin tuple as an `ℓ`-bit string (least significant first). -/
def coinSeq {R ℓ : ℕ} (c : Fin R → Fin (2 ^ ℓ)) (t : ℕ) : List Bool :=
  if h : 1 ≤ t ∧ t ≤ R then List.ofFn (fun s : Fin ℓ => (c ⟨t - 1, by omega⟩ : ℕ).testBit s)
  else []

/-- The coins `c₁, …, c_{t−1}` sent before message `t`. -/
def coinsBefore {R ℓ : ℕ} (c : Fin R → Fin (2 ^ ℓ)) (t : ℕ) : List ℕ :=
  (List.range (t - 1)).map (fun s => if h : s < R then (c ⟨s, h⟩ : ℕ) else 0)

/-- The verifier `V` accepts on instance `q` with `R` rounds, messages `msg` and coins `c`
(public coins: the verifier's messages are the coins themselves). -/
def Accepts (V : Program) (q : Instance) (R ℓ : ℕ) (msg : ℕ → List Bool)
    (c : Fin R → Fin (2 ^ ℓ)) (O : OracleAnswers) : Prop :=
  ∃ o : Outcome, RAMRun V q.encode R msg (coinSeq c) O o ∧ o.accepted = true

/-- `msg` is the honest transcript of prover program `P` for circuit `C`, instance `q` and coins
`c`: each message `t ≤ R` is `P`'s output on the circuit, the instance, `t` and the earlier coins,
with oracle answers `O`. -/
def IsHonestTranscript (P : Program) (C : LayeredCircuit) (q : Instance) (R ℓ : ℕ)
    (c : Fin R → Fin (2 ^ ℓ)) (O : OracleAnswers) (msg : ℕ → List Bool) : Prop :=
  ∀ t, 1 ≤ t → t ≤ R → ∃ time space, SRun P (proverInput C q t (coinsBefore c t)) O (msg t) time space

open Classical in
/-- The **acceptance probability** of verifier `V` against a deterministic adaptive prover
`P* : (t, coins before t) ↦ message t`, over the uniform coin tuple in `(Fin 2^ℓ)^R`. -/
noncomputable def acceptProb (V : Program) (q : Instance) (R ℓ : ℕ)
    (Pstar : ℕ → List ℕ → List Bool) (O : OracleAnswers) : ℝ :=
  ((Finset.univ.filter (fun c : Fin R → Fin (2 ^ ℓ) =>
      Accepts V q R ℓ (fun t => Pstar t (coinsBefore c t)) c O)).card : ℝ) / (2 : ℝ) ^ (ℓ * R)

/-- The oracle-query discipline of Theorem C.1 ("The verifier queries `add~ᵢ` and `mult~ᵢ` once
each per layer", p.33): every query is for a layer `i < L`, and for each layer at most one query
of each type is made. -/
def QueriesOK (L : ℕ) (qs : List Query) : Prop :=
  (∀ q ∈ qs, q.layer < L) ∧
  ∀ i, (qs.filter (fun q => decide (q.layer = i ∧ q.type = 0))).length ≤ 1 ∧
    (qs.filter (fun q => decide (q.layer = i ∧ q.type ≠ 0))).length ≤ 1

/-- Bit `ι` of the two's-complement encoding of width `w` of an integer `z` (the residue
`z mod 2^w`). -/
def twosBit (z : ℤ) (w ι : ℕ) : Bool := ((z % (2 ^ w : ℤ)).toNat).testBit ι

end ApproxGKR


