-- Prove2me | Definitions.Def_QuantumHMMR_IsEfficientlySamplable
-- name    : QuantumHMMR_IsEfficientlySamplable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:04.538521+00:00
-- url     : https://prove2.me/theorems/1d9b789b-1c3b-472b-8553-634409188675
-- title:
--   Efficient sampling of $\nu_n$ by one- and two-qubit gates
-- statement:
--   The one-step law $\nu_n$ is **efficiently samplable** in the following sense.
--
--   1. For some enumeration $e$ of $G$, $\nu_n$ is the law of $\mathrm{decode}(r, i, g, \varphi)$ for a uniform seed $(r, i, g) \in [m] \times [n] \times [|G|]$ and an independent uniform angle $\varphi \in [0, 2\pi)$, where $\mathrm{decode}(r, i, g, \varphi)$ is $e^{i\varphi Z}$ on the first qubit if $r = 0$ (probability $1/m$), and otherwise the gate $e(g)$ on the ring edge $(i, i+1)$.
--   2. The discrete instruction (insertion or not, the wires $i$ and $i + 1 \bmod n$, the gate index) is computed from the binary code of $(n, m, r, i, g)$ by a polynomial-time machine.
--
--   Every output acts on at most two neighbouring qubits.
--
--   **Formalization Note** The angle is an ideal uniform real sample: footnote 4 (p.11) states that a discretization of the angle reproduces the continuous $t$-th moment and omits the details, so no finite-precision implementation is asserted. The discrete seed has $O(\log m + \log n)$ bits.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Theorem 1.3 (statement on p.4); sampler of Section 4, pp.11–12

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_stepLaw
import Definitions.Def_QuantumHMMR_natListCode

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The one-step law `ν_n` of Eq. (8) is efficiently samplable by one- and two-qubit gates
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Theorem 1.3 as stated on p.4: "an efficiently samplable family `{ν_n}_n` of distributions on
one- and two-qubit gates"; the sampler is the one described on pp.11–12).

The two clauses:
1. For some enumeration `e` of `G`, `ν_n` is the law of `decode(r, i, g, φ)` for a uniform seed
   `(r, i, g) ∈ [m] × [n] × [|G|]` and an independent uniform angle `φ ∈ [0, 2π)`, where
   `decode(r, i, g, φ)` is the rotation `e^{iφZ}` on the first qubit if `r = 0` (probability `1/m`),
   and otherwise the gate `e(g) ∈ G` on the ring edge `(i, i + 1)`. Every output acts on at most two
   neighbouring qubits.
2. The discrete instruction (insertion or not; the two wires `i, i + 1 mod n`; the gate index) is
   computed from the binary code of `(n, m, r, i, g)` by a polynomial-time machine.

**Formalization Note** The angle is an ideal uniform real sample: footnote 4 (p.11) says a
discretization of the angle reproduces the continuous `t`-th moment and omits the details, so no
finite-precision implementation is asserted. The seed space has `O(log m + log n)` bits plus the
angle. `nextWire` is the published ring successor. -/
def IsEfficientlySamplable (G : Finset (Clifford.ProjectiveGroup 2)) (n m : ℕ) : Prop :=
  ∃ e : Fin G.card ≃ {g // g ∈ G},
    stepLaw G n m = Measure.map
      (fun s : (Fin m × Fin n × Fin G.card) × ℝ =>
        if s.1.1.val = 0 then firstWireLift n (rotZ s.2)
        else edgeLift s.1.2.1 (Clifford.representative (e s.1.2.2).val).val.val)
      ((ProbabilityTheory.uniformOn (Set.univ : Set (Fin m × Fin n × Fin G.card))).prod
        (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))) ∧
    ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ (r : Fin m) (i : Fin n) (g : Fin G.card),
        f (natListCode [n, m, r.val, i.val, g.val]) =
          natListCode (if r.val = 0 then [0] else [1, i.val, (nextWire i).val, g.val])

end QuantumHMMR


