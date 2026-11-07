-- Prove2me | Definitions.Def_CompNonlocal_Certificate_estimatorError
-- name    : CompNonlocal_Certificate_estimatorError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:45.092716+00:00
-- url     : https://prove2.me/theorems/53e61b70-2502-479f-b5b1-bc2c10eac538
-- title:
--   Error $\eta$ of a receiver-side direction estimator
-- statement:
--   For an estimator that runs the §8.1 receiver on $x$ and then a circuit on $(x,z,Q)$ returning $n\in S^2$,
--   $$\eta:=\mathbb E\big[\|n-r(T)\|_2^2\big],$$
--   with $r(T)$ the Bloch vector of the prepared state given the transcript $T=(x,z)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 15, p.41

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_prepared
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_toQubit
import Definitions.Def_CompNonlocal_blochVec
import Definitions.Def_CompNonlocal_decDir

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The mean squared error `η = E[‖n − r(T)‖²]` of a receiver-side direction estimator in the
§8.1 preparation. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and
Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 15, p.41: an algorithm
"that runs (a, ζ) ← ASP.Rec(x), followed by some computation on (x, a, Q), and returns n ∈ S². Let
η := E[∥n − r(T)∥₂²]."

**Formalization Note** The estimator circuit `Est` reads `x ++ a` (`a` the complete record) and the
prepared qubit `Q`; its classical output is read as a direction by `decDir`. `r(T)` is the Bloch
vector of the normalized prepared state. The expectation is
`Σ_o Σ_z Σ_d Pr[o] · Re Tr(E_d ζ̃_{x,z}) · ‖n_d − r(x, z)‖²`, `x = o.take (lx κ)`; transcripts of
probability `0` have weight `0`. -/
noncomputable def Certificate.estimatorError (c : Certificate) (κ : ℕ) (Est : ICirc) : ℝ :=
  ∑ o : Bits (c.Qg κ).outC.length, ∑ z : Bits (c.A κ).width, ∑ d : Bits Est.outC.length,
    (c.td κ (List.ofFn o)).trace.re *
      (toQubit (Est.effectOn 1 ((List.ofFn o).take (c.lx κ) ++ List.ofFn z)
          (fun t => decide (t = List.ofFn d))) *
        c.prepared κ ((List.ofFn o).take (c.lx κ)) z).trace.re *
      ‖decDir (List.ofFn d) -
          ((c.prepared κ ((List.ofFn o).take (c.lx κ)) z).trace.re)⁻¹ •
            blochVec (c.prepared κ ((List.ofFn o).take (c.lx κ)) z)‖ ^ 2

end CompNonlocal


