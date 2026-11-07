-- Prove2me | Definitions.Def_CompNonlocal_PKE_cpaWin
-- name    : CompNonlocal_PKE_cpaWin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:02.564553+00:00
-- url     : https://prove2.me/theorems/8ffa8b5a-6314-4468-b912-20d63403761f
-- title:
--   Success probability in the IND-CPA experiment
-- statement:
--   $\Pr[b'=b]$ in the experiment: $(pk,sk)\leftarrow\mathrm{KeyGen}(1^\kappa)$; $(m_0,m_1,E)\leftarrow\mathcal A_1(1^\kappa,pk)$ with a retained quantum register $E$; $b\leftarrow\{0,1\}$, $ct\leftarrow\mathrm{Enc}(pk,m_b)$; $b'\leftarrow\mathcal A_2(1^\kappa,pk,ct,E)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 5, p.22

import Mathlib
import Definitions.Def_CompNonlocal_PKE

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The success probability `Pr[b′ = b]` of a two-stage adversary in the IND-CPA experiment.
Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript
(STOC 2027 submission, sha256 e245edd7…), Definition 5, p.22: "1. Generate (pk, sk) ←
PKE.KeyGen(1^κ). 2. Run (m_0, m_1, E) ← A_1(1^κ, pk), where m_0, m_1 ∈ {0,1}^κ are classical and E is
the adversary's retained quantum register. 3. Sample b ← {0, 1} uniformly and compute ct ←
PKE.Enc(pk, m_b). 4. Run b′ ← A_2(1^κ, pk, ct, E)."

**Formalization Note** `A₁` reads `pk`; its classical output `o` gives `m_0 = fit κ o` and
`m_1 = fit κ (o.drop κ)`, and its quantum output is `E`. `A₂` reads `pk ++ ct` and `E`, and `b′` is
its first output bit (`false = 0`). -/
noncomputable def PKE.cpaWin (E : PKE) (κ : ℕ) (A₁ A₂ : ICirc) : ℝ :=
  ∑ pk : Bits (E.KeyGen κ).outC.length, ∑ o : Bits A₁.outC.length, ∑ b : Bool,
    ∑ ct : Bits (E.Enc κ).outC.length,
      (E.sk κ (List.ofFn pk)).trace.re * (1 / 2) *
        E.encProb κ (List.ofFn pk)
          (if b then fit κ ((List.ofFn o).drop κ) else fit κ (List.ofFn o)) (List.ofFn ct) *
        (A₂.effectOn A₁.outQ.length (List.ofFn pk ++ List.ofFn ct)
            (fun t => decide (t.headD false = b)) *
          A₁.branchOn 0 (List.ofFn pk) 1 (fun t => decide (t = List.ofFn o))).trace.re

end CompNonlocal


