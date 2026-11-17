-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_phiS
-- name    : OracleStateHSP_Supplement_phiS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:18.731182+00:00
-- url     : https://prove2.me/theorems/6d8d23a5-87b5-4c68-8748-46a2a11b9ead
-- title:
--   Hard input states $|\varphi^\varepsilon_{H,\alpha}\rangle = \sqrt{1-\varepsilon}|u_G\rangle|0\rangle + e^{i\alpha}\sqrt\varepsilon|H\rangle|1\rangle$ (eq. (70))
-- statement:
--   For a subgroup $H$ of the finite abelian group $G$, a parameter $\varepsilon \in (0, 1]$ and a phase $\alpha \in [0, 2\pi)$, the input state vector of the hard instances is
--   $$
--   |\varphi^\varepsilon_{H,\alpha}\rangle = \sqrt{1-\varepsilon}\, |u_G\rangle|0\rangle + e^{i\alpha}\sqrt{\varepsilon}\, |H\rangle|1\rangle ,
--   $$
--   where $|u_G\rangle = |G|^{-1/2}\sum_{g \in G}|g\rangle$ is the uniform superposition over the group and $|H\rangle = |H|^{-1/2}\sum_{h \in H}|h\rangle$ the uniform superposition over the subgroup. The branch $|H\rangle|1\rangle$ is the only part that depends on $H$ (the informative branch); $|u_G\rangle|0\rangle$ is the uninformative branch.
--
--   **Formalization Note** The basis is $G \times \{0, 1\}$ with the flag as second component.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (70), p.43

import Mathlib

namespace OracleStateHSP

namespace Supplement

open Classical in
/-- The input state vector of the hard instances of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (70), p.43: for a subgroup `H` of
the finite abelian group `G`, `ε ∈ (0, 1]` and a phase `α ∈ [0, 2π)`,
`|φ^ε_(H,α)⟩ = √(1 − ε) |u_G⟩|0⟩ + e^(iα) √ε |H⟩|1⟩`,
with `|u_G⟩ = |G|^(−1/2) ∑_(g∈G) |g⟩` and `|H⟩ = |H|^(−1/2) ∑_(h∈H) |h⟩`.

**Formalization Note.** The basis is `G × Fin 2` (group register, flag qubit); flag `0` is the
uninformative branch, flag `1` the informative one. -/
noncomputable def phiS {G : Type*} [AddGroup G] [Fintype G] (ε : ℝ) (H : AddSubgroup G) (α : ℝ) :
    EuclideanSpace ℂ (G × Fin 2) :=
  WithLp.toLp 2 fun p =>
    if p.2 = 0 then ((Real.sqrt (1 - ε) / Real.sqrt (Fintype.card G) : ℝ) : ℂ)
    else if p.1 ∈ H then
      Complex.exp (α * Complex.I) * ((Real.sqrt ε / Real.sqrt (Nat.card H) : ℝ) : ℂ)
    else 0

end Supplement

end OracleStateHSP


