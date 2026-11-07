-- Prove2me | Definitions.Def_QuantumPRC_diamondDist
-- name    : QuantumPRC_diamondDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:20.057772+00:00
-- url     : https://prove2.me/theorems/811a50ce-834f-4bd9-a050-29c791801da3
-- title:
--   Diamond distance $\|\mathcal E-\mathcal F\|_\diamond$ (with the factor $\tfrac12$)
-- statement:
--   For two CPTP maps $\mathcal E,\mathcal F$ from $A$ to $B$, the paper defines
--
--   $$
--   \|\mathcal E_{A\to B}-\mathcal F_{A\to B}\|_\diamond := \frac12\max_{|\psi\rangle_{RA}}\big\|(\mathrm{id}_R\otimes\mathcal E_{A\to B})(|\psi\rangle\langle\psi|)-(\mathrm{id}_R\otimes\mathcal F_{A\to B})(|\psi\rangle\langle\psi|)\big\|_1 ,
--   $$
--
--   where $R$ has the same dimension as $A$, the maximum is over pure states on $RA$, and $\|\cdot\|_1$ is the trace norm. The factor $\tfrac12$ is part of the definition, so the distance of two channels is at most $1$.
--
--   This is the distance in the robustness condition (43) of PRICs and in the definition of local noise.
--
--   **Formalization Note** $\mathrm{id}_R\otimes\Phi$ is the linear extension of $|i\rangle\langle i'|\otimes|x\rangle\langle x'|\mapsto|i\rangle\langle i'|\otimes\Phi(|x\rangle\langle x'|)$. The maximum is written as a supremum over unit vectors; for CPTP maps the values are bounded by $2$ and the supremum is attained, so it is the printed maximum. The trace norm is the published `WildeQIT.traceNorm`.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.1, p.16

import Mathlib
import Definitions.Def_QuantumPRC_pauliXZ
import Definitions.Def_WildeQIT_traceNorm

open Matrix

namespace QuantumPRC

/-- `id_R ⊗ Φ` for a superoperator `Φ` from `a` to `b` and a reference system with basis `r`,
defined as the linear extension of `|i⟩⟨i'| ⊗ |x⟩⟨x'| ↦ |i⟩⟨i'| ⊗ Φ(|x⟩⟨x'|)`. -/
def tensorId {r a b : Type} [Fintype a] [DecidableEq a] (Φ : Superop a b) :
    Superop (r × a) (r × b) :=
  fun M p q => ∑ x : a, ∑ x' : a, M (p.1, x) (q.1, x') * Φ (Matrix.single x x' 1) p.2 q.2

/-- **Diamond distance.** Hsieh, Yamada, *Quantum Pseudorandom Error-Correcting Codes*,
arXiv:2609.38986 (sha256 6901b59d…), §3.1, p.16: "For two CPTP maps `E, F : A → B`, their
diamond distance is defined by `‖E_{A→B} − F_{A→B}‖⋄ := ½ max_{|ψ⟩_{RA}} ‖(id_R ⊗ E_{A→B})(|ψ⟩⟨ψ|) −
(id_R ⊗ F_{A→B})(|ψ⟩⟨ψ|)‖₁`, where `R` is a register whose dimension is the same as that of `A`, and
the maximization is taken over all pure states on `RA`."

**Formalization Note.** The factor `½` is part of the definition, as printed. `R` is a copy of
`A` (basis `a`), a pure state is a unit vector `ψ : a × a → ℂ`, and `‖·‖₁` is
`WildeQIT.traceNorm`. The maximum is written as a supremum; for the CPTP maps to which it is
applied, the set of values is nonempty and bounded by `2`, and the supremum is attained by
compactness, so it is the printed maximum (on an unbounded set Lean's real supremum would be `0`;
that never happens here). -/
noncomputable def diamondDist {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψ : Superop a b) : ℝ :=
  (1 / 2 : ℝ) * ⨆ ψ : {ψ : a × a → ℂ // ∑ i, ‖ψ i‖ ^ 2 = 1},
    WildeQIT.traceNorm
      (tensorId (r := a) Φ (Matrix.vecMulVec ψ.1 (star ψ.1)) -
        tensorId (r := a) Ψ (Matrix.vecMulVec ψ.1 (star ψ.1)))

end QuantumPRC


