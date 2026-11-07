-- Prove2me | Definitions.Def_CritWinSpin_pkCode
-- name    : CritWinSpin_pkCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:37.920195+00:00
-- url     : https://prove2.me/theorems/55a377d4-10e8-4d9f-b8dd-9d6816d23e0d
-- title:
--   Waters' scheme in the exponent representation: keys, public key, signing, verification
-- statement:
--   Waters' signature scheme on messages $\{0,1\}^d$, in the exponent representation of a bilinear family. **KeyGen**$(1^d)$ draws $\mathrm{desc}$ from the generator and uniform $a,b,u_0,\dots,u_d\in\mathbb Z_q$; the public key is
--   $$P=(G,g,A=g^a,B=g^b,U_0=g^{u_0},\dots,U_d=g^{u_d}),$$
--   coded as a string containing $1^d$, the description and the group-element codes, and the secret key is $K=g^{ab}$. **Sign**$(K,m;r)$ is $(\sigma_1,\sigma_2)=(g^r,K\cdot U(m)^r)$ with $U(m)=U_0\prod_iU_i^{m_i}$. **Verify** accepts exactly when $e(A,B)\,e(\sigma_1,U(m))=e(g,\sigma_2)$, which for $\sigma_j=g^{s_j}$ reads
--   $$ab+s_1u(m)=s_2,\qquad u(m)=u_0+\sum_im_iu_i.$$
--
--   **Formalization Note** The exponents index the key for averaging; the public-key string contains only group-element codes.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §5.1, p.18, eq. (25)

import Mathlib
import Definitions.Def_CritWinSpin_BilinearFamily
open QAlgorithms.Complexity QuantumPRC
set_option autoImplicit false

namespace CritWinSpin

/-- The exponents of a Waters key on messages `{0,1}^d`: `(a, b, u_0, …, u_d)`, §5.1, p.18, so that
`A = g^a`, `B = g^b`, `U_i = g^{u_i}`. -/
abbrev WatersKey (F : BilinearFamily) (desc : Str) (d : ℕ) : Type :=
  Fin (F.q desc) × Fin (F.q desc) × (Fin (d + 1) → Fin (F.q desc))

/-- The expectation of `f` under `KeyGen(1^d)`, §5.1, p.18: draw `desc ← G(1^d)`, then uniform
exponents `a, b, u_0, …, u_d ∈ ℤ_q`. -/
noncomputable def keygenAvg (F : BilinearFamily) (d : ℕ)
    (f : (desc : Str) → WatersKey F desc d → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ (F.gen.coins.eval (unary d).length)) *
    ∑ ω : Fin (F.gen.coins.eval (unary d).length) → Bool,
      let desc := F.gen.alg (tupleCode [List.ofFn ω, unary d])
      (1 / (Fintype.card (WatersKey F desc d) : ℝ)) * ∑ key : WatersKey F desc d, f desc key

/-- **The public key** `P = (G, g, A = g^a, B = g^b, U_0, …, U_d)` as a string, §5.1, p.18. It
contains `1^d`, the group description and the codes of the group elements, and no exponent.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), §5.1, p.18. -/
def pkCode (F : BilinearFamily) (d : ℕ) (desc : Str) (key : WatersKey F desc d) : Str :=
  tupleCode ([unary d, desc, F.encG desc 1, F.encG desc (expo key.1), F.encG desc (expo key.2.1)] ++
    List.ofFn fun i => F.encG desc (expo (key.2.2 i)))

/-- The exponent `u(m) = u_0 + ∑_i m_i u_i` of `U(m) = U_0 ∏_i U_i^{m_i}`, §5.1, p.18. -/
def msgHash {F : BilinearFamily} {d : ℕ} {desc : Str} (key : WatersKey F desc d)
    (m : Fin d → Bool) : ZMod (F.q desc) :=
  expo (key.2.2 0) + ∑ i : Fin d, if m i then expo (key.2.2 i.succ) else 0

/-- The exponent of `σ₂ = K · U(m)^r` for `K = g^{ab}`, §5.1, p.18 (and `σ₁ = g^r`). -/
def signS2 {F : BilinearFamily} {d : ℕ} {desc : Str} (key : WatersKey F desc d)
    (m : Fin d → Bool) (r : ZMod (F.q desc)) : ZMod (F.q desc) :=
  expo key.1 * expo key.2.1 + r * msgHash key m

/-- The verification equation (25), p.18: `e(A, B) e(σ₁, U(m)) = e(g, σ₂)`, read in the exponent of
`e(g, g)` for `σ_j = g^{s_j}`: `ab + s₁ u(m) = s₂`. -/
def IsValidSig {F : BilinearFamily} {d : ℕ} {desc : Str} (key : WatersKey F desc d)
    (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)) : Prop :=
  expo key.1 * expo key.2.1 + s₁ * msgHash key m = s₂

end CritWinSpin


