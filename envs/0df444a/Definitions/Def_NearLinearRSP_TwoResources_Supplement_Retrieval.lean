-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Supplement_Retrieval
-- name    : NearLinearRSP_TwoResources_Supplement_Retrieval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:51.644208+00:00
-- url     : https://prove2.me/theorems/0e342ec6-0a48-44c9-94a6-28ca1771717d
-- title:
--   Deterministic multidimensional potential minimization and witness retrieval
-- statement:
--   For a clock call with retained dimension $d\le k$, write $T(v,i)$ for its computed table, $P$ for the suffix already retrieved, and $i$ for the accumulated tick vector. Define $z=(1+\delta/2)/(1+\delta)$ and the Poisson generating function $g_{uv,r}=\exp(\lambda_rw_r(uv)(z-1))$. The potential is
--   $$
--   \Phi(v,i,P)=T(v,i)+\sum_{r=0}^{d-1}
--   \frac{z^{i_r}}{8k\prod_{uv\in P}g_{uv,r}}.
--   $$
--   Each coordinate starts with weight $1/(8k)$. A virtual tick changes its counter and weight but adds no edge. At a predecessor edge, retrieval chooses the first minimum of the next potential over the full admissible increment rectangle, prepends the predecessor vertex, and updates every counter and generating-function ratio. It returns only after reaching the source; saturation, a malformed parent or exhausted fuel returns no path.
--
--   The total recursion fuel is $(dq+1)(|V_{\rm incident}|+1)+1$. Successful termination within that fuel, genuine path validity and the length/resource bounds are obligations of Theorem 2, rather than input certificates. Extraction ranks handle zero increments; virtual ticks and actual path vertices remain distinct. The definition fixes deterministic witness selection from every retained table.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.10–12, Section 6 deterministic path retrieval and potential, extended by Appendix B p.14

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_Clocks

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def clockZ {k : ℕ} (A : ClockCall k) : ℝ := (1 + A.δ / 2) / (1 + A.δ)

noncomputable def clockPGF {k : ℕ} (A : ClockCall k) (r : Fin A.d) (u v : ℕ) : ℝ :=
  Real.exp (clockMean A r u v * (clockZ A - 1))

/-- Each potential coefficient is 1/(8k), with k the original resource count. -/
noncomputable def multiPotential {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) (P : List ℕ) : ℝ :=
  value A T v i + ∑ r : Fin A.d,
    clockZ A ^ i r / (8 * (k : ℝ) *
      ((P.zip P.tail).map (fun e => clockPGF A r e.1 e.2)).prod)

structure RetrievalState (d : ℕ) where
  path : List ℕ
  counts : Fin d → ℕ
  H : Fin d → ℝ

noncomputable def incrementScore {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (S : RetrievalState A.d) (u v : ℕ) (a : Fin A.d → ℕ) : ℝ :=
  value A T u (fun r => S.counts r + a r) +
    ∑ r, clockZ A ^ a r * S.H r / clockPGF A r u v

/-- A total fuelled specification. Success and sufficient fuel are conclusions
of Theorem 2, never assumed invariants of this routine. -/
noncomputable def retrieveFuel {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) :
    ℕ → RetrievalState A.d → Option (List ℕ)
  | 0, _ => none
  | fuel + 1, S =>
    if ∃ r, A.q ≤ S.counts r then none else
    match S.path.head? with
    | none => none
    | some v =>
      if v = A.I.source then some S.path else
      match (T v S.counts).parent with
      | .none => none
      | .tick j =>
        if h : j < A.d then
          let r : Fin A.d := ⟨j, h⟩
          retrieveFuel A T fuel
            { S with counts := Function.update S.counts r (S.counts r + 1),
                     H := Function.update S.H r (clockZ A * S.H r) }
        else none
      | .edge u =>
        match rectangle A S.counts with
        | [] => none
        | a :: rest =>
          let b := selectMin (incrementScore A T S u v) (a :: rest) a
          retrieveFuel A T fuel
            ⟨u :: S.path, (fun r => S.counts r + b r),
              (fun r => clockZ A ^ b r * S.H r / clockPGF A r u v)⟩

noncomputable def retrieve {k : ℕ} (A : ClockCall k) (t : ℕ) : Option (List ℕ) :=
  retrieveFuel A (constructTable A)
    ((A.d * A.q + 1) * ((incidentVertices A.I).length + 1) + 1)
    ⟨[t], fun _ => 0, fun _ => 1 / (8 * (k : ℝ))⟩

end NearLinearRSP.TwoResources.Supplement


