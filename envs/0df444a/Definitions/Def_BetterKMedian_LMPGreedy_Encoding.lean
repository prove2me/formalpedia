-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_Encoding
-- name    : BetterKMedian_LMPGreedy_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:57.734752+00:00
-- url     : https://prove2.me/theorems/55f54727-10fa-4936-a8a2-6e41f0436168
-- title:
--   Rational UFL instances, their binary code, and a correct $\rho$-LMP output (for Theorem 1.3)
-- statement:
--   `RatInstance`: a UFL instance with rational data — $n$ points `Fin n`, a rational pseudometric `dist`, clients, facilities (a facility whenever there is a client) and a rational opening cost $f\ge0$; `toReal` reads it as an `Instance`. Its binary code `encode` is `encodeNat n`, the client indicator bits, the facility indicator bits, `encodeRat f`, then the $n^2$ distances row-major as `encodeRat`, with `encodeNat`/`encodeRat` of the published `Def_MetricKMedian` (its k-median `Instance` is not reused: it carries $k$ and a strict metric).
--
--   `LMPCorrect ρ I output`: `output` is the indicator bit-list (length $n$) of a set $S$ that meets the $\rho$-LMP guarantee of Definition 2.1 on `I.toReal` (a solution with $\sum_{j\in D}d(j,S)\le\rho(\mathrm{OPT}_f-f|S|)$).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, §2, printed pp. 5–6 (PDF 7–8); Theorem 1.3, printed p. 3 (PDF 5)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_BetterKMedian_LMPGreedy_UFL

set_option autoImplicit false

/-!
# Rational UFL instances, their binary code, and a correct ρ-LMP output (for Theorem 1.3)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, §2 (printed pp. 5–6, PDF 7–8), Definition 2.1, Theorem 1.3 (printed
p. 3, PDF 5).

The paper names no machine model. An algorithm receives a facility-location instance with
rational data, written in binary as in the published `OAI.MetricKMedian.encodeInstance`
(`Definitions.Def_MetricKMedian`, whose `encodeNat`/`encodeRat` are reused): the number `n` of
points, the client and facility indicator bits, the opening cost `f`, and the `n²` distances
row-major. It outputs the indicator bit-list of its facility set `S`.

The instance structure of `Def_MetricKMedian` is not reused: it carries the k-median bound `k`
and requires `d(x, y) = 0 ↔ x = y`, neither of which a UFL instance of this paper has.
-/

namespace BetterKMedian.LMPGreedy

/-- A UFL instance with rational data: points `Fin n`, a rational pseudometric `dist`, clients,
facilities, and a rational uniform opening cost `f ≥ 0`; a facility exists whenever a client
does. -/
structure RatInstance where
  /-- number of points -/
  n : ℕ
  /-- rational distances -/
  dist : Fin n → Fin n → ℚ
  /-- the clients `D` -/
  clients : Finset (Fin n)
  /-- the facilities `F` -/
  facilities : Finset (Fin n)
  /-- the uniform opening cost `f` -/
  f : ℚ
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  f_nonneg : 0 ≤ f
  facilities_nonempty : clients.Nonempty → facilities.Nonempty

namespace RatInstance

/-- The same instance with its data read as real numbers. -/
noncomputable def toReal (I : RatInstance) : Instance where
  N := I.n
  d := fun x y => (I.dist x y : ℝ)
  clients := I.clients
  facilities := I.facilities
  f := (I.f : ℝ)
  d_nonneg := fun x y => by exact_mod_cast I.dist_nonneg x y
  d_self := fun x => by simp [I.dist_self x]
  d_symm := fun x y => by simp [I.dist_symm x y]
  d_triangle := fun x y z => by exact_mod_cast I.dist_triangle x y z
  f_nonneg := by exact_mod_cast I.f_nonneg
  facilities_nonempty := I.facilities_nonempty

/-- The binary code of an instance: `encodeNat n`, the client indicator bits, the facility
indicator bits, `encodeRat f`, then the `n²` distances row-major, each as `encodeRat`. -/
def encode (I : RatInstance) : List Bool :=
  OAI.MetricKMedian.encodeNat I.n ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    OAI.MetricKMedian.encodeRat I.f ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => OAI.MetricKMedian.encodeRat (I.dist i j))).flatten)).flatten

/-- `output` is a correct answer of a `ρ`-LMP approximation algorithm on `I` (Definition 2.1):
it is the indicator bit-list, of length `n`, of a set `S` of points that is a solution
(`S ⊆ F`, nonempty if there is a client) with `Σ_{j ∈ D} d(j, S) ≤ ρ · (OPT_f − f · |S|)`. -/
def LMPCorrect (ρ : ℝ) (I : RatInstance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n),
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧ I.toReal.IsLMPOutput ρ S

end RatInstance

end BetterKMedian.LMPGreedy


