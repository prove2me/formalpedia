-- Prove2me | Definitions.Def_QMCLeafB_numcert_m6
-- name    : QMCLeafB_numcert_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:49:18.366321+00:00
-- url     : https://prove2.me/theorems/6267966c-5fc9-4487-93dd-230c7f3cd23a
-- title:
--   QMCLeafB numcert_m6
-- statement:
--   # leaf B phase 16 — brick `numcert` (swarm `smw1ez4a9`, member m6, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_budget_bound_m1
/-
# leaf B phase 16 — brick `numcert` (swarm `smw1ez4a9`, member m6, direction d7)

The *numeric* side conditions of the final-mile bricks, certified (or refuted) once, in a module the
other bricks can import.  Nothing here rebuilds a state, a program or a run: it is arithmetic about
`Rq`, `eps = Rq/40000`, `dqShallow`, the clip box `2n² + 2dq²`, the rounding cost and the round
count.

What is proved here (see the section headers):

* §1 `dqShallow` is *small*: `dqShallowCore ≤ 1/360000`, `≤ eps`, `9·dq·Rq ≤ eps`, `dqShallow ≤ 1`.
* §2 the campaign clip box `MOfS G = 2n² + 2·dqShallow²`: positive, `≥ 2` at `n ≥ 1` and `≤ 2n²+2`,
  so a clip at `MOfS` is inert on entries of modulus `≤ 1` — the form brick 1 needs.
* §3 **the certified obstruction**: the ok-branch rounding budget
  `roundCost (wMatrixQ G) (3·dq/4) + dq/2 - eps ≤ eps` *forces* `dq ≤ 1/30000`.  Hence `dq = 1` is
  uninstantiable on the interior (`0 < Rq G`): the engine must run at a shallow tolerance.  This is
  the machine-checked form of the campaign's "critical text".
* §4 the value of `Rq` in terms of the request's *encoding*: `Rq G > 0` implies `2^-L ≤ Rq G` with
  `L = (encodeInput G).length`, hence `1/dqShallow ≤ 2^(L+20)` and
  `clog 2 (⌈1/dqShallow⌉ + 1) ≤ L + 21` — the lower-bound half of the fuel/count side.
* §5 **the round count at an arbitrary tolerance**: `budgetRounds_dq_le_clog` bounds the shelf's
  `budgetRounds G dq m` by `((clog 2 ⌈baseA G⌉ + clog 2 ⌈1/dq⌉)·n² + 1)·m`, i.e. the `dq = 1`
  theorem `BudgetBound.budgetRounds_le_clog` with the missing `1/dq` factor.
* §6 the *upper* bound of `Rq` (`Rq ≤ 2^(3L+1)`, `clog 2 (⌈Rq⌉+1) ≤ 3L+2`), which is what turns
  `BudgetBound.budgetRounds_le_monomial`'s leftover hypothesis into a theorem.
* §7 **the unconditional monomial round count**: `budgetRounds G dqShallow m ≤ 34·m·(L+1)·(n+1)³`,
  and the same at `dq = 1` (`budgetRounds_one_le`) — the fuel side condition of brick 1, with no
  hypotheses left.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; audits at the end.
-/

open scoped BigOperators
set_option autoImplicit false

namespace QMCLeafB.NumCert

open QuantumMaxCutEnergy

noncomputable section

/-! ## 1.  The campaign tolerance is small -/

/-- `dqShallowCore G = Rq/(40000·(9·Rq+1))` — the closed form used everywhere below. -/
theorem dqShallowCore_eq (G : Input) :
    QMCLeafB.RundataParams.dqShallowCore G
      = QMCLeafB.EngineRuntime.Rq G
        / (40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)) := by
  rw [QMCLeafB.RundataParams.dqShallowCore, QMCLeafB.RundataCert.eps]
  rw [div_div]

/-- **Smallness of the campaign tolerance.** -/
theorem dqShallowCore_le_inv_360000 (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallowCore G ≤ 1 / 360000 := by
  rw [dqShallowCore_eq G, div_le_iff₀ (by positivity : (0 : ℚ) < 40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1))]
  nlinarith [hRq.le]

/-- The campaign tolerance is at most the leaf's slack `eps G = Rq G/40000`. -/
theorem dqShallowCore_le_eps (G : Input) :
    QMCLeafB.RundataParams.dqShallowCore G ≤ QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.RundataParams.dqShallowCore, QMCLeafB.RundataCert.eps]
  have hden : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by
    have h0 := QMCLeafB.RundataArith.Rq_nonneg G
    linarith
  rw [div_le_iff₀ hden]
  have h0 := QMCLeafB.RundataArith.Rq_nonneg G
  nlinarith

/-- **The tolerance–ledger product.**  `9·dq·Rq ≤ eps`: the decay per round is at most the slack. -/
theorem nine_mul_dqShallowCore_mul_Rq_le (G : Input) :
    9 * QMCLeafB.RundataParams.dqShallowCore G * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.RundataCert.eps G := by
  have hS : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
  have hden : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  rw [QMCLeafB.RundataParams.dqShallowCore, QMCLeafB.RundataCert.eps]
  have h1 : 9 * (QMCLeafB.EngineRuntime.Rq G / 40000 / (9 * QMCLeafB.EngineRuntime.Rq G + 1))
        * QMCLeafB.EngineRuntime.Rq G
      = (9 * (QMCLeafB.EngineRuntime.Rq G / 40000) * QMCLeafB.EngineRuntime.Rq G)
        / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
    field_simp
  rw [h1, div_le_iff₀ hden]
  have h2 : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 := by positivity
  nlinarith

/-- The fallback-free form: at `Rq ≠ 0` the campaign tolerance *is* the core formula. -/
theorem dqShallow_eq_core (G : Input) (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.RundataParams.dqShallow G = QMCLeafB.RundataParams.dqShallowCore G := by
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg hRq]

/-- `dqShallow ≤ 1` for every input (the fallback is exactly `1`). -/
theorem dqShallow_le_one (G : Input) : QMCLeafB.RundataParams.dqShallow G ≤ 1 := by
  unfold QMCLeafB.RundataParams.dqShallow
  split_ifs with h
  · rfl
  · rcases lt_or_eq_of_le (QMCLeafB.RundataArith.Rq_nonneg G) with h1 | h1
    · have h2 := dqShallowCore_le_inv_360000 G h1
      linarith
    · exact absurd h1.symm h

/-- `dqShallow² ≤ 1`. -/
theorem dqShallow_sq_le_one (G : Input) : QMCLeafB.RundataParams.dqShallow G ^ 2 ≤ 1 := by
  have h0 : (0 : ℚ) ≤ QMCLeafB.RundataParams.dqShallow G := (QMCLeafB.RundataParams.dqShallow_pos G).le
  have h1 := dqShallow_le_one G
  nlinarith

/-! ## 2.  The campaign clip box `2n² + 2·dq²` -/

/-- The clip box of the campaign run: `mu = 2n² + 2·dqShallow²`. -/
noncomputable def MOfS (G : Input) : ℚ :=
  2 * (G.n : ℚ) ^ 2 + 2 * (QMCLeafB.RundataParams.dqShallow G) ^ 2

/-- The defining equation, in the shape the engine's `initShapeOf` names it. -/
theorem MOfS_eq (G : Input) : MOfS G = 2 * (G.n : ℚ) ^ 2 + 2 * (QMCLeafB.RundataParams.dqShallow G) ^ 2 :=
  rfl

theorem MOfS_pos (G : Input) : 0 < MOfS G := by
  unfold MOfS
  have := QMCLeafB.RundataParams.dqShallow_pos G
  positivity

/-- At `n ≥ 1` the campaign clip box is at least `2`. -/
theorem MOfS_ge_two (G : Input) (hn : 1 ≤ G.n) : 2 ≤ MOfS G := by
  unfold MOfS
  have h1 : (1 : ℚ) ≤ (G.n : ℚ) := by exact_mod_cast hn
  have h2 : (0 : ℚ) ≤ QMCLeafB.RundataParams.dqShallow G :=
    (QMCLeafB.RundataParams.dqShallow_pos G).le
  nlinarith

/-- The campaign clip box is at most the old `dq = 1` box `2n²+2`: shrinking `dq` only shrinks it. -/
theorem MOfS_le (G : Input) : MOfS G ≤ 2 * (G.n : ℚ) ^ 2 + 2 := by
  unfold MOfS
  have h := dqShallow_sq_le_one G
  nlinarith

/-- **Clip inertness, in the form brick 1 needs**: at `n ≥ 1` every entry of modulus `≤ 1` is inside
the campaign clip box `2n² + 2·dqShallow²`. -/
theorem abs_le_MOfS (G : Input) (hn : 1 ≤ G.n) {q : ℚ} (h : |q| ≤ 1) : |q| ≤ MOfS G := by
  have h1 := MOfS_ge_two G hn
  have h2 : (0 : ℚ) ≤ |q| := abs_nonneg q
  linarith

/-! ## 3.  The certified obstruction: `dq = 1` cannot pay the rounding budget -/

/-- `roundCost` at the weight matrix dominates `2·ν·Rq`. -/
theorem two_mul_roundCost_le (G : Input) {ν : ℚ} (hν : 0 ≤ ν) :
    2 * ν * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) ν := by
  rw [QMCLeafB.RundataCert.roundCost_wMatrixQ]
  have hS : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
  have hcoef : 2 * ν ≤ (1 + ν) * (2 * ν + ν ^ 2) := by nlinarith [hν, sq_nonneg ν, mul_nonneg hν hν]
  calc 2 * ν * QMCLeafB.EngineRuntime.Rq G
      ≤ ((1 + ν) * (2 * ν + ν ^ 2)) * QMCLeafB.EngineRuntime.Rq G :=
        mul_le_mul_of_nonneg_right hcoef hS
    _ = (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|) := by
        rw [QMCLeafB.RundataCert.sum_abs_wMatrixQ]

/-- **Any tolerance that pays the ok-branch rounding budget is at most `1/30000`.**  The budget is
`roundCost A (3·dq/4) + dq/2 - ε ≤ ε`; since `roundCost ≥ (3/2)·dq·Rq` and `ε = Rq/40000`, it forces
`dq ≤ 2·(2ε)/(3·Rq) = 1/30000`. -/
theorem budget_forces_dq_le (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) {dq' : ℚ}
    (h0 : 0 ≤ dq')
    (h : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * dq' / 4)
        + dq' / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G) :
    dq' ≤ 1 / 30000 := by
  have hν : (0 : ℚ) ≤ 3 * dq' / 4 := by linarith
  have hcost := two_mul_roundCost_le G hν
  have heps : QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl
  have h3 : 3 * dq' / 2 * QMCLeafB.EngineRuntime.Rq G
      ≤ QMCLeafB.EngineRuntime.Rq G / 20000 := by
    have h4 : 2 * (3 * dq' / 4) * QMCLeafB.EngineRuntime.Rq G
        = 3 * dq' / 2 * QMCLeafB.EngineRuntime.Rq G := by ring
    rw [h4] at hcost
    rw [heps] at h
    nlinarith
  have h5 : 3 * dq' / 2 ≤ 1 / 20000 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < (3 * dq' / 2 - 1 / 20000) * QMCLeafB.EngineRuntime.Rq G :=
      mul_pos (by linarith) hRq
    nlinarith
  linarith

/-- **`dq = 1` is not admissible on the interior.**  The rounding budget that `RunData.hcert`
carries is unsatisfiable at slack `1` as soon as the graph has positive total weight. -/
theorem one_not_admissible (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    ¬ (QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * (1 : ℚ) / 4)
        + 1 / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G) := by
  intro h
  have hle := budget_forces_dq_le G hRq (by norm_num : (0 : ℚ) ≤ 1) h
  norm_num at hle


/-! ## 4.  `Rq` from below, by the encoded length of the request -/

theorem le_two_pow_encodeNat (k : ℕ) : k ≤ 2 ^ (Computability.encodeNat k).length := by
  have h : (Computability.encodeNat k).length = Nat.size k := by
    rw [QMCNumericRuntime.encodeNat_eq_bits, Nat.size_eq_bits_len]
  rw [h]
  exact (Nat.size_le.mp (le_refl k.size)).le

theorem le_two_pow_encodeNumber (k : ℕ) :
    k ≤ 2 ^ (QuantumMaxCutEnergy.encodeNumber k).length := by
  have hlen : (QuantumMaxCutEnergy.encodeNumber k).length
      = 2 * (Computability.encodeNat k).length + 1 := by
    simp only [QuantumMaxCutEnergy.encodeNumber, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    ring
  rw [hlen]
  calc k ≤ 2 ^ (Computability.encodeNat k).length := le_two_pow_encodeNat k
    _ ≤ 2 ^ (2 * (Computability.encodeNat k).length + 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega

/-- The bits of one matrix entry, exactly as `encodeInput` writes them. -/
def block (G : Input) (i j : Fin G.n) : List Bool :=
  if hij : i < j then
    let q := G.weights ⟨(i, j), hij⟩
    QuantumMaxCutEnergy.encodeNumber q.num ++ QuantumMaxCutEnergy.encodeNumber q.den
  else []

theorem encodeInput_eq (G : Input) :
    QuantumMaxCutEnergy.encodeInput G
      = List.replicate G.n true ++ [false]
        ++ (List.finRange G.n).flatMap
            (fun i => (List.finRange G.n).flatMap (fun j => block G i j)) := by
  simp only [QuantumMaxCutEnergy.encodeInput, block]

theorem length_block_le_inner (G : Input) (i j : Fin G.n) :
    (block G i j).length
      ≤ ((List.finRange G.n).flatMap (fun j => block G i j)).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem
    (List.mem_map_of_mem (f := fun j => (block G i j).length) (List.mem_finRange j))

theorem length_block_le_outer (G : Input) (i j : Fin G.n) :
    (block G i j).length
      ≤ ((List.finRange G.n).flatMap
          (fun i => (List.finRange G.n).flatMap (fun j => block G i j))).length := by
  rw [List.length_flatMap]
  refine le_trans (length_block_le_inner G i j) (List.le_sum_of_mem ?_)
  exact List.mem_map_of_mem
    (f := fun i => ((List.finRange G.n).flatMap (fun j => block G i j)).length)
    (List.mem_finRange i)

theorem length_block_le_encodeInput (G : Input) (i j : Fin G.n) :
    (block G i j).length ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
  rw [encodeInput_eq G, List.length_append]
  exact le_trans (length_block_le_outer G i j) (Nat.le_add_left _ _)

theorem block_spec (G : Input) (e : Edge G.n) :
    block G e.val.1 e.val.2
      = QuantumMaxCutEnergy.encodeNumber ((G.weights e).num)
        ++ QuantumMaxCutEnergy.encodeNumber ((G.weights e).den) := by
  obtain ⟨⟨i, j⟩, hij⟩ := e
  simp only [block, dif_pos hij]

theorem weight_ge_inv_two_pow (G : Input) (e : Edge G.n)
    (he : 0 < ((G.weights e : ℚ≥0) : ℚ)) :
    (1 : ℚ) / 2 ^ (QuantumMaxCutEnergy.encodeInput G).length
      ≤ ((G.weights e : ℚ≥0) : ℚ) := by
  have hnum : 1 ≤ (G.weights e).num := NNRat.num_pos.mpr he
  have hdenpos : 0 < (G.weights e).den := (G.weights e).den_pos
  have hblocklen : (QuantumMaxCutEnergy.encodeNumber (G.weights e).num
      ++ QuantumMaxCutEnergy.encodeNumber (G.weights e).den).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
    rw [← block_spec G e]
    exact length_block_le_encodeInput G e.val.1 e.val.2
  have hdenlen : (QuantumMaxCutEnergy.encodeNumber (G.weights e).den).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
    have h := hblocklen
    simp only [List.length_append] at h
    omega
  have hdenNat : (G.weights e).den ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    refine le_trans (le_two_pow_encodeNumber (G.weights e).den) ?_
    exact Nat.pow_le_pow_right (by norm_num) hdenlen
  have hdenQ : ((G.weights e).den : ℚ) ≤ (2 : ℚ) ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    exact_mod_cast hdenNat
  have hcast : ((G.weights e : ℚ≥0) : ℚ)
      = ((G.weights e).num : ℚ) / ((G.weights e).den : ℚ) := NNRat.cast_def _
  rw [hcast]
  have h1 : (1 : ℚ) / ((G.weights e).den : ℚ)
      ≤ ((G.weights e).num : ℚ) / ((G.weights e).den : ℚ) := by
    apply div_le_div_of_nonneg_right _ (by exact_mod_cast hdenpos.le : (0:ℚ) ≤ ((G.weights e).den : ℚ))
    exact_mod_cast hnum
  have h2 : (1 : ℚ) / (2 : ℚ) ^ (QuantumMaxCutEnergy.encodeInput G).length
      ≤ 1 / ((G.weights e).den : ℚ) := by
    apply one_div_le_one_div_of_le _ hdenQ
    exact_mod_cast hdenpos
  linarith

theorem Rq_ge_inv_two_pow (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (1 : ℚ) / 2 ^ (QuantumMaxCutEnergy.encodeInput G).length
      ≤ QMCLeafB.EngineRuntime.Rq G := by
  have hsum : 0 < ∑ e, ((G.weights e : ℚ≥0) : ℚ) := by
    have h : QMCLeafB.EngineRuntime.Rq G = 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ) := rfl
    rw [h] at hRq
    linarith
  have hex : ∃ e, 0 < ((G.weights e : ℚ≥0) : ℚ) := by
    by_contra h
    push Not at h
    have hle : ∑ e, ((G.weights e : ℚ≥0) : ℚ) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => h i)
    linarith
  obtain ⟨e, he⟩ := hex
  have h1 := weight_ge_inv_two_pow G e he
  have h3 : ((G.weights e : ℚ≥0) : ℚ) ≤ ∑ e, ((G.weights e : ℚ≥0) : ℚ) :=
    Finset.single_le_sum (f := fun e => ((G.weights e : ℚ≥0) : ℚ))
      (fun i _ => by positivity) (Finset.mem_univ e)
  have h : QMCLeafB.EngineRuntime.Rq G = 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ) := rfl
  rw [h]
  have h4 : (0 : ℚ) < (1 : ℚ) / 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by positivity
  linarith

/-- **The tolerance in input-length form.**  `1/dqShallow ≤ 2^(L+20)` with `L` the length of the
encoded request: the shallow tolerance is never smaller than an inverse power of two of the input
size. -/
theorem inv_dqShallow_le (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (1 : ℚ) / QMCLeafB.RundataParams.dqShallow G
      ≤ (2 : ℚ) ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) := by
  have hRqne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := hRq.ne'
  have hpos : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := hRq
  have h1 : (1 : ℚ) / 2 ^ (QuantumMaxCutEnergy.encodeInput G).length
      ≤ QMCLeafB.EngineRuntime.Rq G := Rq_ge_inv_two_pow G hRq
  rw [QMCLeafB.NumCert.dqShallow_eq_core G hRqne, QMCLeafB.NumCert.dqShallowCore_eq G]
  have key : (1 : ℚ) / (QMCLeafB.EngineRuntime.Rq G
        / (40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)))
      = 360000 + 40000 * (1 / QMCLeafB.EngineRuntime.Rq G) := by
    field_simp
    ring
  rw [key]
  have h2L : (0 : ℚ) < 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by positivity
  have h3 : (1 : ℚ) / QMCLeafB.EngineRuntime.Rq G
      ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    rw [div_le_iff₀ hpos]
    have hm := mul_le_mul_of_nonneg_left h1 h2L.le
    rw [mul_one_div, div_self h2L.ne'] at hm
    linarith
  have h4 : 40000 * (1 / QMCLeafB.EngineRuntime.Rq G)
      ≤ 40000 * 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    nlinarith [h3]
  have h5 : (1 : ℚ) ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    have := Nat.one_le_two_pow (n := (QuantumMaxCutEnergy.encodeInput G).length)
    have : ((1 : ℕ) : ℚ) ≤ ((2 ^ (QuantumMaxCutEnergy.encodeInput G).length : ℕ) : ℚ) := by
      exact_mod_cast this
    simpa using this
  have h6 : (2 : ℚ) ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20)
      = 2 ^ (QuantumMaxCutEnergy.encodeInput G).length * 1048576 := by
    rw [pow_add]
    norm_num
  rw [h6]
  nlinarith [h4, h5]

/-- **The input-length form of the round-count's `clog`**: `clog 2 (⌈1/dq⌉+1) ≤ L+21`. -/
theorem clog_inv_dqShallow_le (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    Nat.clog 2 (Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G) + 1)
      ≤ (QuantumMaxCutEnergy.encodeInput G).length + 21 := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  have h1 := inv_dqShallow_le G hRq
  have hcast : ((2 : ℚ) ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20))
      = ((2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) : ℕ) : ℚ) := by
    push_cast
    ring
  have h2 : Nat.ceil (1 / QMCLeafB.RundataParams.dqShallow G)
      ≤ 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) :=
    Nat.ceil_le.mpr (hcast ▸ h1)
  have h3 : (1 : ℕ) ≤ 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) :=
    Nat.one_le_two_pow
  have h4 : 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) + 1
      ≤ 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 21) := by
    have e1 : 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 21)
        = 2 * 2 ^ ((QuantumMaxCutEnergy.encodeInput G).length + 20) := by
      rw [show (QuantumMaxCutEnergy.encodeInput G).length + 21
          = (QuantumMaxCutEnergy.encodeInput G).length + 20 + 1 from by omega, pow_succ]
      ring
    rw [e1]
    omega
  omega


/-! ## 5.  The round count at an arbitrary tolerance -/

/-- The base of the run at tolerance `dq`: `2Φ₀/r^N = 2·(baseAq G dq)^N`. -/
def baseAq (G : Input) (dq : ℚ) : ℝ :=
  Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
    * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / (dq : ℝ))

theorem two_pot_div_dq (G : Input) {dq : ℚ} (hdq : 0 < dq) :
    2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
      / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * (baseAq G dq) ^ (G.n * G.n) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by positivity
  rw [QMCLeafB.Boundary.volPot_initShapeOf _ hM]
  have hdiv : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
      / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))))
      = baseAq G dq := by
    unfold baseAq
    field_simp
  have hdivpow : (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))) ^ (G.n * G.n)
        / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = (baseAq G dq) ^ (G.n * G.n) := by
    rw [← div_pow, hdiv]
  calc 2 * (Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))) ^ (G.n * G.n)
        / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      = 2 * ((Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))) ^ (G.n * G.n)
          / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))) := by
        ring
    _ = 2 * (baseAq G dq) ^ (G.n * G.n) := by rw [hdivpow]

theorem baseAq_le_baseA (G : Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1) :
    baseAq G dq ≤ QMCLeafB.BudgetBound.baseA G * (1 / dq) := by
  unfold baseAq QMCLeafB.BudgetBound.baseA QMCLeafB.BudgetBound.MOf
  have hsqrt : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
      ≤ Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hq : dq ^ 2 ≤ (1 : ℚ) ^ 2 := by rw [one_pow]; nlinarith
    have hle : (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) ≤ (2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) := by linarith
    exact_mod_cast hle
  have h8 : (0 : ℝ) ≤ 8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) := by
    have h0 : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
    have : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by exact_mod_cast h0
    linarith
  have hdqR : (0 : ℝ) < (dq : ℝ) := by exact_mod_cast hdq
  calc Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / (dq : ℝ))
      ≤ Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / (dq : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ) : ℝ))
        * (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1)) * (1 / dq) := by
        rw [mul_one_div]
        ring

theorem baseAq_nonneg (G : Input) {dq : ℚ} (hdq : 0 < dq) : 0 ≤ baseAq G dq := by
  unfold baseAq
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply div_nonneg _ (by exact_mod_cast hdq.le)
  have h0 : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
  have h1 : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by exact_mod_cast h0
  linarith

theorem budgetRounds_dq_le_clog (G : Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) * m := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by positivity
  have hdqR : (0 : ℝ) < (dq : ℝ) := by exact_mod_cast hdq
  have hbase := baseAq_le_baseA G hdq hdq1
  have hbase1 : (0 : ℝ) < QMCLeafB.BudgetBound.baseA G := by
    have := QMCLeafB.BudgetBound.one_le_baseA G
    linarith
  have hab : baseAq G dq ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)))
      * (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq))) := by
    refine le_trans hbase ?_
    have h1 : QMCLeafB.BudgetBound.baseA G ≤ ((Nat.ceil (QMCLeafB.BudgetBound.baseA G) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((Nat.ceil (QMCLeafB.BudgetBound.baseA G) : ℕ) : ℝ)
        ≤ ((2 ^ Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    have h3 : (1 / dq : ℚ) ≤ ((Nat.ceil (1 / dq) : ℕ) : ℚ) := Nat.le_ceil _
    have h3' : ((1 : ℚ) / dq : ℝ) ≤ ((Nat.ceil (1 / dq) : ℕ) : ℝ) := by exact_mod_cast h3
    have h4 : ((Nat.ceil (1 / dq) : ℕ) : ℝ)
        ≤ ((2 ^ Nat.clog 2 (Nat.ceil (1 / dq)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    have h5 : ((1 : ℚ) / dq : ℝ) = 1 / (dq : ℝ) := by push_cast; ring
    have hb : (1 / (dq : ℝ)) ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq))) := by
      have h2' : ((2 ^ Nat.clog 2 (Nat.ceil (1 / dq)) : ℕ) : ℝ)
          = (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq))) := by push_cast; ring
      linarith [h3', h4, h2', h5]
    have ha : QMCLeafB.BudgetBound.baseA G ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))) := by
      have h2' : ((2 ^ Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)) : ℕ) : ℝ)
          = (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))) := by push_cast; ring
      linarith
    calc QMCLeafB.BudgetBound.baseA G * (1 / dq)
        ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))) * (1 / (dq : ℝ)) := by
          apply mul_le_mul_of_nonneg_right ha (div_nonneg zero_le_one hdqR.le)
      _ ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)))
            * (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq))) := by
          apply mul_le_mul_of_nonneg_left hb (by positivity)
  have hX : 2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
      / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n))
      ≤ (2 : ℝ) ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) := by
    rw [two_pot_div_dq G hdq]
    have hpow : (baseAq G dq) ^ (G.n * G.n) ≤ ((2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)))
        * (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq)))) ^ (G.n * G.n) := by
      exact pow_le_pow_left₀ (baseAq_nonneg G hdq) hab (G.n * G.n)
    have hEq : ((2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)))
        * (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq)))) ^ (G.n * G.n)
        = (2 : ℝ) ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n)) := by
      rw [← pow_add, ← pow_mul]
    calc 2 * (baseAq G dq) ^ (G.n * G.n)
        ≤ 2 * ((2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)))
            * (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (1 / dq)))) ^ (G.n * G.n) := by
          linarith
      _ = 2 * (2 : ℝ) ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n)) := by rw [hEq]
      _ = (2 : ℝ) ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) := by
          rw [pow_succ]
          ring
  have hceil : Nat.ceil (2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
      / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n)))
      ≤ 2 ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) := by
    refine Nat.ceil_le.mpr ?_
    have hc : (((2 ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) : ℕ)) : ℝ)
        = (2 : ℝ) ^ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
            + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) := by
      push_cast
      ring
    rw [hc]
    exact hX
  have hdef : QMCLeafB.FinalStroke.budgetRounds G dq m
      = Nat.clog 2 (Nat.ceil (2 * QMCLeafB.EngineIterates.volPot (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2))
          / ((((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n)))) * m := rfl
  rw [hdef]
  apply Nat.mul_le_mul_right
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hceil

/-! ## 6.  `Rq` from above, by the encoded length — the `clog` of the round count -/

/-- Every weight is at most `2^L`: `w = num/den ≤ num ≤ 2^|encodeNumber num|`. -/
theorem weight_le_two_pow (G : Input) (e : Edge G.n) :
    ((G.weights e : ℚ≥0) : ℚ) ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
  have hblocklen : (QuantumMaxCutEnergy.encodeNumber (G.weights e).num
      ++ QuantumMaxCutEnergy.encodeNumber (G.weights e).den).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
    rw [← block_spec G e]
    exact length_block_le_encodeInput G e.val.1 e.val.2
  have hnumlen : (QuantumMaxCutEnergy.encodeNumber (G.weights e).num).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
    have h := hblocklen
    simp only [List.length_append] at h
    omega
  have hnum : (G.weights e).num ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    refine le_trans (le_two_pow_encodeNumber (G.weights e).num) ?_
    exact Nat.pow_le_pow_right (by norm_num) hnumlen
  have hcast : ((G.weights e : ℚ≥0) : ℚ)
      = ((G.weights e).num : ℚ) / ((G.weights e).den : ℚ) := NNRat.cast_def _
  have hden1 : (1 : ℚ) ≤ ((G.weights e).den : ℚ) := by exact_mod_cast (G.weights e).den_pos
  have hnumQ : ((G.weights e).num : ℚ) ≤ (2 : ℚ) ^ (QuantumMaxCutEnergy.encodeInput G).length := by
    exact_mod_cast hnum
  rw [hcast]
  calc ((G.weights e).num : ℚ) / ((G.weights e).den : ℚ) ≤ ((G.weights e).num : ℚ) / 1 := by
        apply div_le_div_of_nonneg_left _ (by norm_num) hden1
        exact_mod_cast (G.weights e).num.zero_le
    _ = ((G.weights e).num : ℚ) := by ring
    _ ≤ (2 : ℚ) ^ (QuantumMaxCutEnergy.encodeInput G).length := hnumQ

/-- `n` is at most the length of the encoding (the unary prefix). -/
theorem n_le_length_encodeInput (G : Input) : G.n ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
  rw [QuantumMaxCutEnergy.encodeInput]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The encoding is nonempty. -/
theorem one_le_length_encodeInput (G : Input) :
    1 ≤ (QuantumMaxCutEnergy.encodeInput G).length := by
  rw [QuantumMaxCutEnergy.encodeInput]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- `L ≤ 2^L`. -/
theorem length_le_two_pow_length (G : Input) :
    (QuantumMaxCutEnergy.encodeInput G).length
      ≤ 2 ^ (QuantumMaxCutEnergy.encodeInput G).length := by
  have h1 : (QuantumMaxCutEnergy.encodeInput G).length
      ≤ 2 ^ Nat.clog 2 (QuantumMaxCutEnergy.encodeInput G).length :=
    Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 (QuantumMaxCutEnergy.encodeInput G).length
      ≤ (QuantumMaxCutEnergy.encodeInput G).length :=
    QMCLeafB.BudgetBound.clog_two_le_self (one_le_length_encodeInput G)
  exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) h2)

/-- `Rq` is at most `2^(3L+1)`. -/
theorem Rq_le_two_pow (G : Input) :
    QMCLeafB.EngineRuntime.Rq G
      ≤ (2 : ℚ) ^ (3 * (QuantumMaxCutEnergy.encodeInput G).length + 1) := by
  set L := (QuantumMaxCutEnergy.encodeInput G).length with hL
  have hsum : ∑ e, ((G.weights e : ℚ≥0) : ℚ) ≤ ∑ _e : Edge G.n, (2 : ℚ) ^ L :=
    Finset.sum_le_sum (fun e _ => weight_le_two_pow G e)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card (Edge G.n) : ℚ) ≤ (G.n : ℚ) * (G.n : ℚ) := by
    have h1 : Fintype.card (Edge G.n) ≤ Fintype.card (Fin G.n × Fin G.n) :=
      Fintype.card_subtype_le _
    have h2 : Fintype.card (Fin G.n × Fin G.n) = G.n * G.n := by
      simp [Fintype.card_prod]
    have h3 : Fintype.card (Edge G.n) ≤ G.n * G.n := le_trans h1 (le_of_eq h2)
    exact_mod_cast h3
  have hnL : (G.n : ℚ) ≤ (L : ℚ) := by exact_mod_cast n_le_length_encodeInput G
  have hL1 : (1 : ℚ) ≤ (L : ℚ) := by exact_mod_cast one_le_length_encodeInput G
  have hLL : (L : ℚ) ≤ (2 : ℚ) ^ L := by
    have h := length_le_two_pow_length G
    rw [← hL] at h
    exact_mod_cast h
  have hnn : (G.n : ℚ) * (G.n : ℚ) ≤ (2 : ℚ) ^ (2 * L) := by
    have hsq : (G.n : ℚ) * (G.n : ℚ) ≤ (L : ℚ) * (L : ℚ) := by nlinarith
    have h2 : (L : ℚ) * (L : ℚ) ≤ (2 : ℚ) ^ (2 * L) := by
      have h3 : ((2 : ℚ) ^ L) * ((2 : ℚ) ^ L) = (2 : ℚ) ^ (L + L) := (pow_add _ _ _).symm
      have h4 : (L : ℚ) * (L : ℚ) ≤ ((2 : ℚ) ^ L) * ((2 : ℚ) ^ L) := by
        apply mul_self_le_mul_self (by linarith : (0:ℚ) ≤ (L:ℚ)) hLL
      rw [h3] at h4
      rw [show 2 * L = L + L from by ring]; exact h4
    linarith
  have hRq : QMCLeafB.EngineRuntime.Rq G = 2 * ∑ e, ((G.weights e : ℚ≥0) : ℚ) := rfl
  rw [hRq]
  have hpow : (2 : ℚ) ^ (3 * L + 1) = 2 * ((2 : ℚ) ^ (2 * L) * (2 : ℚ) ^ L) := by
    rw [show 3 * L + 1 = 2 * L + L + 1 from by ring, pow_add, pow_add]
    ring
  rw [hpow]
  have h2L : (0 : ℚ) ≤ (2 : ℚ) ^ (2 * L) := by positivity
  have h2L' : (0 : ℚ) < (2 : ℚ) ^ L := by positivity
  nlinarith [hsum, hcard, hnn, h2L, h2L']

/-- `clog 2 (⌈Rq⌉+1) ≤ 3L+2`. -/
theorem clog_Rq_le (G : Input) :
    Nat.clog 2 (Nat.ceil (QMCLeafB.EngineRuntime.Rq G) + 1)
      ≤ 3 * (QuantumMaxCutEnergy.encodeInput G).length + 2 := by
  refine (Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_
  set L := (QuantumMaxCutEnergy.encodeInput G).length with hL
  have hRq := Rq_le_two_pow G
  have hlt : QMCLeafB.EngineRuntime.Rq G ≤ ((2 ^ (3 * L + 2) - 1 : ℕ) : ℚ) := by
    have h3 : (1 : ℕ) ≤ 2 ^ (3 * L + 2) := Nat.one_le_two_pow
    have h4 : ((2 ^ (3 * L + 2) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (3 * L + 2) - 1 := by
      push_cast [h3]
      ring
    rw [h4, show 3 * L + 2 = 3 * L + 1 + 1 from by ring, pow_succ]
    have h2k : (1 : ℚ) ≤ (2 : ℚ) ^ (3 * L + 1) := by
      have hh := Nat.one_le_two_pow (n := 3 * L + 1)
      have hh' : ((1 : ℕ) : ℚ) ≤ ((2 ^ (3 * L + 1) : ℕ) : ℚ) := by exact_mod_cast hh
      simpa using hh'
    nlinarith [h2k]
  have h1 : Nat.ceil (QMCLeafB.EngineRuntime.Rq G) ≤ 2 ^ (3 * L + 2) - 1 := Nat.ceil_le.mpr hlt
  have h2 : (1 : ℕ) ≤ 2 ^ (3 * L + 2) := Nat.one_le_two_pow
  omega

/-- **The round count as a monomial**, with the input-length bound on the inverse tolerance passed
in.  `16·(n+1)³·(L+1)` dominates the round factor for every input. -/
theorem budgetRounds_le_monomial_of (G : Input) {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq ≤ 1) (m : ℕ)
    {B : ℕ} (hb : Nat.clog 2 (Nat.ceil (1 / dq) + 1) ≤ B)
    (hB : B ≤ (QuantumMaxCutEnergy.encodeInput G).length + 21) :
    QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ 34 * m * ((QuantumMaxCutEnergy.encodeInput G).length + 1) * (G.n + 1) ^ 3 := by
  set L := (QuantumMaxCutEnergy.encodeInput G).length with hL
  have hL1 : 1 ≤ L := one_le_length_encodeInput G
  have hnL : G.n ≤ L := n_le_length_encodeInput G
  have hmain := budgetRounds_dq_le_clog G hdq hdq1 m
  have hb' : Nat.clog 2 (Nat.ceil (1 / dq)) ≤ B :=
    le_trans (Nat.clog_mono_right 2 (Nat.le_succ _)) hb
  have ha : Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G)) ≤ 3 * L + G.n + 8 := by
    have h1 := QMCLeafB.BudgetBound.clog_baseA_le G
    have h2 := clog_Rq_le G
    omega
  have hkey : (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
        + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1
      ≤ 34 * ((L + 1) * (G.n + 1) ^ 3) := by
    have hsum : Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
        + Nat.clog 2 (Nat.ceil (1 / dq)) ≤ 4 * L + G.n + 29 := by omega
    have hN : G.n * G.n ≤ (G.n + 1) ^ 3 := by nlinarith
    have h1 : (Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
        + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) ≤ (4 * L + G.n + 29) * ((G.n + 1) ^ 3) := by
      apply Nat.mul_le_mul hsum hN
    have h2 : 4 * L + G.n + 29 ≤ 33 * (L + 1) := by omega
    have h3 : (4 * L + G.n + 29) * ((G.n + 1) ^ 3) ≤ 33 * (L + 1) * ((G.n + 1) ^ 3) :=
      Nat.mul_le_mul_right _ h2
    have h4 : 33 * (L + 1) * ((G.n + 1) ^ 3) + 1 ≤ 34 * ((L + 1) * ((G.n + 1) ^ 3)) := by
      have hpos : 1 ≤ (L + 1) * ((G.n + 1) ^ 3) := by
        have : 1 ≤ (G.n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
        have : 1 ≤ L + 1 := by omega
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    omega
  calc QMCLeafB.FinalStroke.budgetRounds G dq m
      ≤ ((Nat.clog 2 (Nat.ceil (QMCLeafB.BudgetBound.baseA G))
          + Nat.clog 2 (Nat.ceil (1 / dq))) * (G.n * G.n) + 1) * m := hmain
    _ ≤ (34 * ((L + 1) * (G.n + 1) ^ 3)) * m := Nat.mul_le_mul_right m hkey
    _ = 34 * m * ((QuantumMaxCutEnergy.encodeInput G).length + 1) * (G.n + 1) ^ 3 := by
        rw [← hL]; ring

/-- **The round count at the campaign tolerance, unconditionally monomial.**  At
`dq = dqShallow G` the round factor of the run is dominated by `34·m·(L+1)·(n+1)³` with
`L = |encodeInput G|`.  This is the fuel side condition of the init brick. -/
theorem budgetRounds_dqShallow_le (G : Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G) m
      ≤ 34 * m * ((QuantumMaxCutEnergy.encodeInput G).length + 1) * (G.n + 1) ^ 3 := by
  have hdq : 0 < QMCLeafB.RundataParams.dqShallow G := QMCLeafB.RundataParams.dqShallow_pos G
  have hdq1 : QMCLeafB.RundataParams.dqShallow G ≤ 1 := dqShallow_le_one G
  refine budgetRounds_le_monomial_of G hdq hdq1 m ?_ (le_refl _)
  rcases lt_or_eq_of_le (QMCLeafB.RundataArith.Rq_nonneg G) with hpos | hzero
  · exact clog_inv_dqShallow_le G hpos
  · have h1 : QMCLeafB.RundataParams.dqShallow G = 1 := by
      unfold QMCLeafB.RundataParams.dqShallow
      rw [if_pos hzero.symm]
    rw [h1]
    have hcz : Nat.clog 2 (Nat.ceil (1 / (1 : ℚ)) + 1) = 1 := by
      have hce : Nat.ceil (1 / (1 : ℚ)) = 1 := by
        rw [div_one]
        norm_num
      rw [hce]
      have hp : Nat.clog 2 (2 ^ 1) = 1 := Nat.clog_pow 2 1 (by norm_num)
      simpa using hp
    rw [hcz]
    omega

/-- **The round count at slack `1`**, the `dq = 1` case of `BudgetBound.budgetRounds_le_monomial`
with its hypothesis discharged. -/
theorem budgetRounds_one_le (G : Input) (m : ℕ) :
    QMCLeafB.FinalStroke.budgetRounds G 1 m
      ≤ 34 * m * ((QuantumMaxCutEnergy.encodeInput G).length + 1) * (G.n + 1) ^ 3 := by
  refine budgetRounds_le_monomial_of G (by norm_num) (le_refl 1) m ?_ (le_refl _)
  have hcz : Nat.clog 2 (Nat.ceil (1 / (1 : ℚ)) + 1) = 1 := by
    have hce : Nat.ceil (1 / (1 : ℚ)) = 1 := by
      rw [div_one]
      norm_num
    rw [hce]
    have hp : Nat.clog 2 (2 ^ 1) = 1 := Nat.clog_pow 2 1 (by norm_num)
    simpa using hp
  rw [hcz]
  omega


/-! ## 8.  The audit finding about the campaign's snap grid

The state's snap grid at the init is `d = (n+1)^4` (m8's `gridOf`, `dOf` in m1's init, `stD` of the
init state).  The campaign tolerance is at most `1/360000`, *independently of `n`* — so for a small
graph the snap step is thousands of times coarser than `dqShallow`:

    n = 2:  snap step 1/81 against dqShallow = 1/380000  (a factor 4700),
    n ≥ 24: the grid is finally finer than the tolerance.

Hence **no side condition of the form `1/d ≤ c·dq` can hold on the campaign grid below `n = 24`**;
the run-of-program agreement must either use an adaptive dyadic surrogate for its query centre
(`QMCLeafB.CentreTrack.hdrift_of_dyadic` keeps the per-round `grid` free) or the init must set
`stD` from `dqShallow` — which is harmless size-wise, since `1/dqShallow ≤ 2^(L+20)` (§4). -/

/-- **The general form**: any natural grid coarser than `1/360000` is coarser than the campaign
tolerance. -/
theorem dqShallowCore_lt_inv_nat (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) {d : ℕ}
    (hd0 : 0 < d) (hd : d < 360000) :
    QMCLeafB.RundataParams.dqShallowCore G < 1 / (d : ℚ) := by
  have h2 := dqShallowCore_le_inv_360000 G hRq
  have hdQ : (d : ℚ) < 360000 := by exact_mod_cast hd
  have hd0Q : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd0
  have h5 : (1 : ℚ) / 360000 < 1 / (d : ℚ) := one_div_lt_one_div_of_lt hd0Q hdQ
  linarith

/-- The snap step `1/(n+1)^4` exceeds the campaign tolerance whenever `(n+1)^4 < 360000` (that is,
for all `n ≤ 23`). -/
theorem dqShallow_lt_inv_grid (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hgrid : (G.n + 1) ^ 4 < 360000) :
    QMCLeafB.RundataParams.dqShallow G < 1 / (((G.n + 1) ^ 4 : ℕ) : ℚ) := by
  have h1 : QMCLeafB.RundataParams.dqShallow G = QMCLeafB.RundataParams.dqShallowCore G :=
    dqShallow_eq_core G hRq.ne'
  have h0 : 0 < (G.n + 1) ^ 4 := by positivity
  rw [h1]
  exact dqShallowCore_lt_inv_nat G hRq h0 hgrid

/-- A lower bound for the campaign tolerance when the total weight is at least one:
`dqShallowCore ≥ 1/400000`. -/
theorem dqShallowCore_ge (G : Input) (hRq : 1 ≤ QMCLeafB.EngineRuntime.Rq G) :
    (1 : ℚ) / 400000 ≤ QMCLeafB.RundataParams.dqShallowCore G := by
  have hRq0 : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := by linarith
  rw [dqShallowCore_eq G,
    le_div_iff₀ (by positivity : (0 : ℚ) < 40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1))]
  nlinarith

/-- The other side, with a hypothesis on the weight: from `n ≥ 25` and `Rq ≥ 1` on, the campaign
grid `(n+1)^4` is finer than the tolerance.  (The converse of `dqShallow_lt_inv_grid` is *false* for
small `Rq`: `dqShallowCore ≈ Rq/40000` there, so no bound on `n` alone can make the grid fine
enough.) -/
theorem inv_grid_le_dqShallow (G : Input) (hRq : 1 ≤ QMCLeafB.EngineRuntime.Rq G)
    (hn : 25 ≤ G.n) :
    1 / (((G.n + 1) ^ 4 : ℕ) : ℚ) ≤ QMCLeafB.RundataParams.dqShallow G := by
  set D : ℕ := (G.n + 1) ^ 4 with hD
  have hDge : (400000 : ℕ) ≤ D := by
    have hle : 26 ≤ G.n + 1 := by omega
    have hp := Nat.pow_le_pow_left hle 4
    norm_num at hp
    rw [hD]
    omega
  have hdQ : (400000 : ℚ) ≤ (D : ℚ) := by exact_mod_cast hDge
  have h6 : (1 : ℚ) / (D : ℚ) ≤ 1 / 400000 :=
    one_div_le_one_div_of_le (a := (400000 : ℚ)) (by norm_num) hdQ
  have h7 := dqShallowCore_ge G hRq
  have h1 : QMCLeafB.RundataParams.dqShallow G = QMCLeafB.RundataParams.dqShallowCore G :=
    dqShallow_eq_core G (by linarith : QMCLeafB.EngineRuntime.Rq G ≠ 0)
  rw [h1]
  linarith

end

/-! ## Axiom audit -/

#print axioms QMCLeafB.NumCert.dqShallowCore_eq
#print axioms QMCLeafB.NumCert.dqShallowCore_le_inv_360000
#print axioms QMCLeafB.NumCert.dqShallowCore_le_eps
#print axioms QMCLeafB.NumCert.nine_mul_dqShallowCore_mul_Rq_le
#print axioms QMCLeafB.NumCert.dqShallow_le_one
#print axioms QMCLeafB.NumCert.dqShallow_sq_le_one
#print axioms QMCLeafB.NumCert.MOfS_pos
#print axioms QMCLeafB.NumCert.MOfS_ge_two
#print axioms QMCLeafB.NumCert.MOfS_le
#print axioms QMCLeafB.NumCert.abs_le_MOfS
#print axioms QMCLeafB.NumCert.two_mul_roundCost_le
#print axioms QMCLeafB.NumCert.budget_forces_dq_le
#print axioms QMCLeafB.NumCert.one_not_admissible
#print axioms QMCLeafB.NumCert.le_two_pow_encodeNumber
#print axioms QMCLeafB.NumCert.length_block_le_encodeInput
#print axioms QMCLeafB.NumCert.weight_ge_inv_two_pow
#print axioms QMCLeafB.NumCert.Rq_ge_inv_two_pow
#print axioms QMCLeafB.NumCert.inv_dqShallow_le
#print axioms QMCLeafB.NumCert.clog_inv_dqShallow_le
#print axioms QMCLeafB.NumCert.two_pot_div_dq
#print axioms QMCLeafB.NumCert.baseAq_le_baseA
#print axioms QMCLeafB.NumCert.budgetRounds_dq_le_clog
#print axioms QMCLeafB.NumCert.weight_le_two_pow
#print axioms QMCLeafB.NumCert.Rq_le_two_pow
#print axioms QMCLeafB.NumCert.clog_Rq_le
#print axioms QMCLeafB.NumCert.budgetRounds_le_monomial_of
#print axioms QMCLeafB.NumCert.budgetRounds_dqShallow_le
#print axioms QMCLeafB.NumCert.budgetRounds_one_le
#print axioms QMCLeafB.NumCert.dqShallow_lt_inv_grid
#print axioms QMCLeafB.NumCert.inv_grid_le_dqShallow
#print axioms QMCLeafB.NumCert.dqShallowCore_ge

end QMCLeafB.NumCert


