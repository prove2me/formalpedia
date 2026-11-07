-- Prove2me | Definitions.Def_MMSDelta2_CircuitMMSLang
-- name    : MMSDelta2_CircuitMMSLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:23.008433+00:00
-- url     : https://prove2.me/theorems/429e75fe-9e90-4834-b360-d7611583ed19
-- title:
--   Circuit valuations and their MMS existence problem (Proposition 4.1)
-- statement:
--   A **circuit valuation** on $m$ goods consists of a sign circuit $C_{\mathrm{sgn}}$ and magnitude circuits $C_0,\dots,C_{b-1}$, all Boolean circuits with $m$ inputs. On a bundle $S$ with characteristic vector $\chi_S\in\{0,1\}^m$ its value is the signed integer
--
--   $$v(S)=(-1)^{C_{\mathrm{sgn}}(\chi_S)}\sum_{k=0}^{b-1}C_k(\chi_S)\,2^k,$$
--
--   i.e. the circuits output the value of $S$ as a signed integer in binary (sign and magnitude bits). Values may be negative, and $v$ need not be monotone or satisfy $v(\emptyset)=0$.
--
--   For an instance with $n$ agents having circuit valuations, $\mathrm{MMS}_i$ is the maximum over all partitions of the goods into $n$ bundles of the minimum value of a bundle, and an MMS allocation is an allocation (pairwise disjoint bundles covering all goods) giving every agent $i$ value at least $\mathrm{MMS}_i$. The language $\mathrm{CircuitMMS}$ is the set of codes of instances with $n\ge1$ agents with circuit valuations that admit an MMS allocation.
--
--   **Formalization Note** Circuits are the published `KarpLiptonOM.Circuit`. A circuit with $s$ gates is encoded by the code of $s$ followed by the published `circuitCode m s`; an instance by $n$, $m$ and, agent by agent, the sign circuit, the number $b$ and the $b$ magnitude circuits.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Proposition 4.1, p.11 (PDF p.13); proof pp.56–57 (PDF pp.58–59)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_KarpLiptonOM_circuitCode
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_RRFair_Setting
import Definitions.Def_MMSDelta2_instCode

namespace MMSDelta2

/-!
# Circuit valuations and the MMS existence problem for them (Proposition 4.1)

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), Proposition 4.1, p.11 (PDF p.13): "valuations
represented by circuits that, given the characteristic vector of a bundle, output its value as a
signed integer in binary"; proof pp.56–57 (PDF pp.58–59).

**Formalization Note.**
* A circuit valuation on `m` goods is a sign circuit and a list of `b` magnitude circuits, all
  published `KarpLiptonOM.Circuit m`. On a bundle `S` with characteristic vector `χ_S` (a list of `m`
  bits, good `g` at position `g`) its value is `(−1)^{sign(χ_S)} · Σ_{k<b} bit_k(χ_S) · 2^k`:
  sign-magnitude binary, the output bits computed by `b` single-output circuits. Values may be
  negative; the valuation need not be monotone or normalized.
* `MMS_i` is `LittleCharity.MMS.mms` of the circuit valuation (all labelled partitions into `n`
  bundles); allocations are pairwise disjoint and cover all goods.
* A circuit `C` is encoded by the code of its number of gates `s` followed by the published
  `circuitCode m s C`; an instance by `n`, `m` and, agent by agent, the sign circuit, the number `b`
  and the `b` magnitude circuits. The language contains exactly the codes of instances with `n ≥ 1`
  admitting an MMS allocation.
-/

/-- A valuation of `m` goods represented by circuits: a sign circuit and magnitude-bit circuits. -/
structure CircuitVal (m : ℕ) where
  /-- the circuit computing the sign bit (`true` = negative) -/
  sign : KarpLiptonOM.Circuit m
  /-- the circuits computing the magnitude bits, least significant first -/
  mag : List (KarpLiptonOM.Circuit m)

/-- The characteristic vector of a bundle `S` of `m` goods. -/
def charVec {m : ℕ} (S : Finset (Fin m)) : List Bool := List.ofFn fun g => decide (g ∈ S)

/-- The value of bundle `S` under the circuit valuation `c` (a signed integer). -/
def CircuitVal.value {m : ℕ} (c : CircuitVal m) (S : Finset (Fin m)) : ℤ :=
  (if c.sign.eval (charVec S) then -1 else 1) *
    (c.mag.mapIdx fun k C => if C.eval (charVec S) then (2 : ℤ) ^ k else 0).sum

/-- The code of a circuit: its number of gates `s`, then `circuitCode m s C`. -/
def circCode {m : ℕ} (C : KarpLiptonOM.Circuit m) : List Bool :=
  natCode C.gates.length ++ KarpLiptonOM.circuitCode m C.gates.length C

/-- The code of a circuit valuation: sign circuit, number of magnitude bits, magnitude circuits. -/
def circuitValCode {m : ℕ} (c : CircuitVal m) : List Bool :=
  circCode c.sign ++ natCode c.mag.length ++ (c.mag.map circCode).flatten

/-- The code of an instance with `n` agents with circuit valuations on `m` goods. -/
def circuitInstCode (n m : ℕ) (c : Fin n → CircuitVal m) : List Bool :=
  natCode n ++ natCode m ++ (List.ofFn fun i => circuitValCode (c i)).flatten

/-- The circuit instance `c` admits an MMS allocation. -/
def HasCircuitMMSAllocation {n m : ℕ} (c : Fin n → CircuitVal m) : Prop :=
  ∃ A : Fin n → Finset (Fin m), StrategicAlloc.RRFair.IsAllocation A ∧
    ∀ i, LittleCharity.MMS.mms (fun S => ((c i).value S : ℝ)) n Finset.univ ≤ ((c i).value (A i) : ℝ)

/-- Codes of circuit-valuation instances (`n ≥ 1`) that admit an MMS allocation. -/
def CircuitMMSLang : Set (List Bool) :=
  {w | ∃ (n m : ℕ) (c : Fin n → CircuitVal m), 1 ≤ n ∧ HasCircuitMMSAllocation c ∧
    w = circuitInstCode n m c}

end MMSDelta2


