-- Prove2me | Definitions.Def_TorchFire_TF_witnessProb
-- name    : TorchFire_TF_witnessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:47:54.57632+00:00
-- url     : https://prove2.me/theorems/029245ca-fb61-4673-a1d2-e0d777c85e22
-- title:
--   Witness procedures and $p_{\mathrm{wit}}$ of Lemma 8.5
-- statement:
--   A **witness procedure** $A^W$ (Lemma 8.5) follows the issuance rules of Definition 6.2: a first stage on the $v$ pre-split flames measures a torch request $J$, $|J|=m$; a second stage on its retained register, only the $m$ issued torches $(T_j)_{j\in J}$ and the $N$ challenge flames (all flames may be processed jointly) outputs $m+1$ witnesses. A witness (88) is $(s',t,\sigma_T)$ with $s'=(\ell',a')$; it is **valid** if $t\in T_{\mathrm{pub}}$ and $\mathrm{OSS.Ver}^{O_T}(t,M_T(s',t),\sigma_T)=1$, and its label is $\ell'$.
--
--   $$p_{\mathrm{wit}}=\Pr[A^W \text{ outputs valid witnesses for } m+1 \text{ distinct labels}],$$
--   with a setup abort counting as failure.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 8.5 p.74; (86), (88) p.70

import Mathlib
import Definitions.Def_TorchFire_TF_splitWinProb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- The torch-signature fields of a witness (88), p.70: the serial `s′ = (ℓ′, a′)` of the request, the
torch key `t`, and the torch signature `σ_T` (the signed message is `M_T(s′, t)`). -/
abbrev WitData (lam : ℕ) : Type := Serial lam × Key lam × (Fin (L lam) → Sig lam)

instance (lam : ℕ) : Fintype (WitData lam) := inferInstance
instance (lam : ℕ) : DecidableEq (WitData lam) := inferInstance

variable {lam R m N v : ℕ}

/-- A **valid witness** (88): `t ∈ T_pub` and `OSS.Ver^{O_T}(t, M_T(s′, t), σ_T) = 1`; its label is
`ℓ′`. -/
def ValidWit (ω : Sample lam R) (w : WitData lam) : Prop :=
  InTpub ω w.2.1 ∧ longVer (OT ω) w.2.1 (msgT w.1 w.2.1) w.2.2

noncomputable instance (ω : Sample lam R) (w : WitData lam) : Decidable (ValidWit ω w) :=
  Classical.dec _

/-- **A witness procedure `A^W`** (Lemma 8.5, p.74), following the issuance rules of Definition 6.2:
the first stage receives the `v` pre-split flames and measures a torch request `J` (`|J| = m`); the
second stage receives its retained register, only the `m` issued torches `(T_j)_{j ∈ J}`, and the `N`
challenge flames (it may process all flames jointly), and outputs `m + 1` witnesses. Both stages query
the full public collection (47). -/
structure WitnessAdv (lam R m N v : ℕ) where
  Ret1 : Type
  [instFRet1 : Fintype Ret1]
  [instDRet1 : DecidableEq Ret1]
  st1 : (Fin v → Serial lam) →
    OracleAlg (Fin v → Flame lam) (TorchSet R m × Ret1) (PubDom lam R) (PubAns lam)
  st2 : (Fin v → Serial lam) → (Fin N → Serial lam) → TorchSet R m →
    OracleAlg ((Ret1 × (Fin m → AReg lam)) × (Fin N → Flame lam)) (Fin (m + 1) → WitData lam)
      (PubDom lam R) (PubAns lam)

attribute [instance] WitnessAdv.instFRet1 WitnessAdv.instDRet1

/-- The witness procedure makes at most `Q` public-oracle queries in total. -/
def WitnessAdv.QueryBounded (A : WitnessAdv lam R m N v) (Q : ℕ) : Prop :=
  ∀ ss ss' J, (A.st1 ss).T + (A.st2 ss ss' J).T ≤ Q

/-- **`p_wit = Pr[A^W outputs valid witnesses for m + 1 distinct labels]`** (Lemma 8.5, p.74): every
output witness is valid and their labels are pairwise distinct; a setup abort counts as failure. -/
noncomputable def witProb (A : WitnessAdv lam R m N v) : ℝ :=
  avg (Sample lam R) fun ω =>
    if SetupOK ω then
      ∑ ss : Fin v → Serial lam, ∑ ss' : Fin N → Serial lam, ∑ J : TorchSet R m,
        let σ1 := (A.st1 ss).run (pubOracle ω) (piKron fun j => block (sparkCQ ω) (ss j))
        let out := (A.st2 ss ss' J).run (pubOracle ω)
          (Matrix.of fun x y => block σ1 J x.1.1 y.1.1 * torchesOf ω J.1 J.2 x.1.2 y.1.2 *
            ∏ i, block (sparkCQ ω) (ss' i) (x.2 i) (y.2 i))
        ∑ w : Fin (m + 1) → WitData lam,
          if (∀ h, ValidWit ω (w h)) ∧ Function.Injective (fun h => (w h).1.1) then
            (out w w).re else 0
    else 0

end TorchFire.TF


