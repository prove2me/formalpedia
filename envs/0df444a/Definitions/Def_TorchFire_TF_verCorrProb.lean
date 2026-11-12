-- Prove2me | Definitions.Def_TorchFire_TF_verCorrProb
-- name    : TorchFire_TF_verCorrProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:47:31.361888+00:00
-- url     : https://prove2.me/theorems/65701c5c-2908-4607-9dee-56481882a314
-- title:
--   Torch-fire verification correctness (32) and cloning correctness (33)
-- statement:
--   The correctness experiments of Definition 6.1 for Construction 7.4.
--
--   1. **Verification correctness** (32): sample $O\leftarrow\mathrm{TF.GenOracles}(1^\lambda,1^R)$, run $\mathrm{TF.Setup}$ (an abort counts as failure), $(s,F)\leftarrow\mathrm{TF.Spark}^O(sk)$, and accept iff $\mathrm{TF.Ver}^O(pk,s,F)=1$.
--   2. **Cloning correctness** (33) for the torch $j\in[R]$: after setup and spark, set $T^{(0)}=T_j$ and execute $(T^{(i)},F_{i-1},F_i)\leftarrow\mathrm{TF.Clone}^O(pk,t_j,s,T^{(i-1)},F_{i-1})$ for $i=1,\dots,q$ (the first returned flame replaces the input register); the probability that $\mathrm{TF.Ver}^O(pk,s,F_i)=1$ for all $i=0,\dots,q$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Definition 6.1 (32)–(33) pp.44–45

import Mathlib
import Definitions.Def_TorchFire_TF_cloneTF

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **Verification correctness probability** (32), Definition 6.1, p.45 (Chatterjee–Mukherjee–
Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256
4e43d2f2…afd593), for Construction 7.4: sample `O ← TF.GenOracles(1^λ, 1^R)`, run `TF.Setup^O(1^λ,
1^R)` (an abort counts as failure), `(s, F) ← TF.Spark^O(sk)`, and accept iff `TF.Ver^O(pk, s, F) = 1`. -/
noncomputable def verCorrProb (lam R : ℕ) : ℝ :=
  avg (Sample lam R) fun ω =>
    if SetupOK ω then ∑ s : Serial lam, accProb (verEff ω s) (block (sparkCQ ω) s) else 0

/-- The effect "all `q + 1` flames verify under `s`" on the state of the cloning loop: the `q`
returned flames and the current `(T, F_q)` (the torch is not tested). -/
noncomputable def allVerEff {lam R : ℕ} (ω : Sample lam R) (s : Serial lam) (q : ℕ) :
    Matrix ((Fin q → Flame lam) × (AReg lam × Flame lam))
      ((Fin q → Flame lam) × (AReg lam × Flame lam)) ℂ :=
  Matrix.of fun x y =>
    (∏ i, verEff ω s (x.1 i) (y.1 i)) * (if x.2.1 = y.2.1 then 1 else 0) * verEff ω s x.2.2 y.2.2

/-- **Cloning correctness probability** (33), Definition 6.1, p.45, for Construction 7.4 and the torch
`j ∈ [R]`: after setup and `(s, F_0) ← TF.Spark^O(sk)`, set `T^{(0)} = T_j` and execute
`(T^{(i)}, F_{i−1}, F_i) ← TF.Clone^O(pk, t_j, s, T^{(i−1)}, F_{i−1})` for `i = 1, …, q` (the first
returned flame replaces the input register); then check `TF.Ver^O(pk, s, F_i)` for `i = 0, …, q`. A
setup abort counts as failure. -/
noncomputable def cloneCorrProb (lam R q : ℕ) (j : Fin R) : ℝ :=
  avg (Sample lam R) fun ω =>
    if SetupOK ω then
      ∑ s : Serial lam,
        accProb (allVerEff ω s q)
          (chain (cloneTF ω (tk ω j) s)
            (Matrix.of fun x y => torchState ω j x.1 y.1 * block (sparkCQ ω) s x.2 y.2) q)
    else 0

end TorchFire.TF


