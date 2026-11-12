-- Prove2me | Definitions.Def_TorchFire_TF_Rce
-- name    : TorchFire_TF_Rce
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:44:57.201599+00:00
-- url     : https://prove2.me/theorems/4f308503-499c-429d-b0fb-843fa68e653d
-- title:
--   The coherent affine query $R^O_{c,e}=(S^O_{c,e})^\dagger U_\Gamma S^O_{c,e}$ (97), the ideal query, and $e_A$, $e_T$, $e_{\mathrm{tag}}$, $d$
-- statement:
--   **App. C.1.** For a serial $s=(\ell,a)$, a torch key $t$, a component $c$ and $e\in\{0,1\}$, the preparation circuit $S^O_{c,e}$ (i) computes $z_q=\mathrm{enc}(\mathrm{forward},\mathrm{code}(q))$ into a fresh register $Z$ ($q=(s,t,c,e,u)$, $u$ read from the affine registers); (ii) applies $\mathrm{Fire.Tag}^O$ to the CGS flame part $K=YU$ with request register $Z$; (iii) applies the coherent long-message signers $U^{O_{A,\ell}}_{a,M_A(s,t)}$ to the anchor $A$ and $U^{O_T}_{t,M_T(s,t)}$ to the torch $T$. Then $\Gamma$ is queried on $(q,(Y,R_0,R_1),\Sigma_A,\Sigma_T)$ into the answer register of $e$, and $(S^O_{c,e})^\dagger$ is applied:
--   $$R^O_{c,e}=(S^O_{c,e})^\dagger U_\Gamma S^O_{c,e}\qquad(97).$$
--   The affine registers of one component are $X$ ($n-r$ qubits), $Y$ ($k$ qubits) and the ⊥ flags of the two answers; the ideal query $U_{\mathrm{affine}_{a_c,e}}$ writes $\mathrm{affine}_{a_c,e}(u)$ into the answer register (App. C.2).
--
--   The module also defines the error terms of §7.2: $e_A=\sum_c\sum_b\epsilon_{a_c,b}$ and $e_T=\sum_j\sum_c\sum_b\epsilon_{t_{j,c},b}$ (50), $e_{\mathrm{tag}}$ (51) for $O_K$, $d=\min\{1,e_A+e_T+e_{\mathrm{tag}}\}$ (53), and $e(\lambda)=2^{-\lambda}+2^{-(n-r)}$.
--
--   **Formalization Note** The paper also copies $q$ into a register $Q$ that $\Gamma$ reads and $S^\dagger$ uncomputes; reading $s,t,c,e$ as parameters of the call and $u$ from the affine registers gives the same operator. In $e_{\mathrm{tag}}$ the register $E$ is trivial: the supremum of the quadratic form $\langle\psi|(M_Z\otimes I_E)|\psi\rangle$ does not depend on $E$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), App. C.1 (97) pp.83–84; App. C.2 p.84; (50)–(51) p.54; (53) p.55

import Mathlib
import Definitions.Def_TorchFire_TF_Sample
import Definitions.Def_TorchFire_CGS_tagErr

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- A long-message signing register `R_1 ⋯ R_L` (an anchor `A` or a torch `T`), (39), p.49. -/
abbrev AReg (lam : ℕ) : Type := Fin (L lam) → Bits (k lam)

/-- The resources of an affine query: anchor `A`, torch `T`, CGS flame part `K` (App. C.1, p.83). -/
abbrev Res (lam : ℕ) : Type := AReg lam × AReg lam × CGS.KReg (muK lam)

/-- **The affine registers of one anchor component** in the preparation circuit (42): `X` (`n − r`
qubits, the input `w` of `affine_{y,0}` and the answer of `affine_{y,1}`), `Y` (`k` qubits, the answer of
`affine_{y,0}` and the input of `affine_{y,1}`), and the ⊥ flags of the two answers. -/
abbrev AffPair (lam : ℕ) : Type := Bits (nr lam) × Bits (k lam) × ZMod 2 × ZMod 2

/-- **The fresh auxiliary registers of one coherent affine query** (App. C.1, p.83): the query
register `Z` for `z_q`, the tag workspace `E_0 Σ_0 R_0 E_1 Σ_1 R_1`, and the signing workspaces and
signature registers `Σ_A`, `Σ_T` of the anchor and torch signers. -/
abbrev RWs (lam : ℕ) : Type :=
  Bits (CGS.ell (muK lam)) × CGS.TagWs (muK lam) × (Fin (L lam) → SignWs lam × Sig lam) ×
    (Fin (L lam) → SignWs lam × Sig lam)

/-- The registers acted on by `R^O_{c,e}`. -/
abbrev RSpace (lam : ℕ) : Type := Res lam × AffPair lam × RWs lam

instance (lam : ℕ) : Fintype (AReg lam) := inferInstance
instance (lam : ℕ) : DecidableEq (AReg lam) := inferInstance
instance (lam : ℕ) : Fintype (Res lam) := inferInstance
instance (lam : ℕ) : DecidableEq (Res lam) := inferInstance
instance (lam : ℕ) : Fintype (AffPair lam) := inferInstance
instance (lam : ℕ) : DecidableEq (AffPair lam) := inferInstance
instance (lam : ℕ) : Fintype (RWs lam) := inferInstance
instance (lam : ℕ) : DecidableEq (RWs lam) := inferInstance
instance (lam : ℕ) : Fintype (RSpace lam) := inferInstance
instance (lam : ℕ) : DecidableEq (RSpace lam) := inferInstance

variable {lam R : ℕ}

/-- The zero state of the auxiliary registers. -/
def rws0 : RWs lam := (0, CGS.tagWs0, fun _ => (0, none), fun _ => (0, none))

/-- The affine input held in the registers: `w = X` for `e = 0`, `u = Y` for `e = 1`. -/
def affIn (e : ZMod 2) (p : AffPair lam) : AffIn lam :=
  if e = 0 then .inl p.1 else .inr p.2.1

/-- Write an oracle answer (flag, slots) into the answer register of `e`: for `e = 0` into the flag
of `affine_{·,0}` and `Y`; for `e = 1` into the flag of `affine_{·,1}` and `X`. -/
def writeAns (e : ZMod 2) (p : AffPair lam) (ans : ZMod 2 × GammaAns lam) : AffPair lam :=
  if e = 0 then (p.1, p.2.1 + ans.2.1, p.2.2.1 + ans.1, p.2.2.2)
  else (p.1 + ans.2.2, p.2.1, p.2.2.1, p.2.2.2 + ans.1)

/-- **The preparation circuit `S^O_{c,e}`** (App. C.1, pp.83–84; Chatterjee–Mukherjee–Pathak–Podder,
*Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593), for the
serial `s = (ℓ, a)`, torch key `t`, component `c` and bit `e`:

(i) compute `z_q = enc(forward, code(q))`, `q = (s, t, c, e, u)`, into `Z` (the affine input `u` is
    read from the affine registers, which are left unchanged);
(ii) apply `Fire.Tag^O` (95) to `K = YU` with request register `Z` (tag in `(Y, R_0, R_1)`);
(iii) apply the coherent long-message signers `U^{O_{A,ℓ}}_{a, M_A(s,t)}` to `A` and
    `U^{O_T}_{t, M_T(s,t)}` to `T`, with signatures in `Σ_A`, `Σ_T`.

**Formalization Note** The paper also copies `q` into a register `Q` that `Γ` reads and `S†`
uncomputes; here `Γ` reads `s, t, c, e` (classical parameters of the call) and `u` from the affine
registers directly, which gives the same operator `R^O_{c,e}`. -/
noncomputable def Sprep (ω : Sample lam R) (s : Serial lam) (t : Key lam) (c : Fin (L lam))
    (e : ZMod 2) : Matrix (RSpace lam) (RSpace lam) ℂ :=
  let gz := basisMat fun x : RSpace lam =>
    (x.1, x.2.1, (x.2.2.1 + zq s t c e (affIn e x.2.1), x.2.2.2))
  let gtag := liftOn (fun x : RSpace lam =>
      ((x.1.2.2, x.2.2.1, x.2.2.2.1), (x.1.1, x.1.2.1, x.2.1, x.2.2.2.2)))
    (CGS.tag (OK ω))
  let gA := liftOn (fun x : RSpace lam =>
      ((fun c' => (x.1.1 c', (x.2.2.2.2.1 c').1, (x.2.2.2.2.1 c').2)),
        (x.1.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2)))
    (longSignU (OA ω s.1) s.2 (msgA s t))
  let gT := liftOn (fun x : RSpace lam =>
      ((fun c' => (x.1.2.1 c', (x.2.2.2.2.2 c').1, (x.2.2.2.2.2 c').2)),
        (x.1.1, x.1.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1)))
    (longSignU (OT ω) t (msgT s t))
  gT * gA * gtag * gz

/-- The `Γ` query of the coherent affine call: inputs `(q, (Y, R_0, R_1), Σ_A, Σ_T)`, answer register
of `e` (App. C.1, p.84). -/
noncomputable def gammaQuery (ω : Sample lam R) (s : Serial lam) (t : Key lam) (c : Fin (L lam))
    (e : ZMod 2) : Matrix (RSpace lam) (RSpace lam) ℂ :=
  basisMat fun x : RSpace lam =>
    let g : GammaDom lam :=
      (s, t, c, e, affIn e x.2.1, CGS.tagOf (x.1.2.2, x.2.2.1, x.2.2.2.1),
        fun c' => (x.2.2.2.2.1 c').2, fun c' => (x.2.2.2.2.2 c').2)
    (x.1, writeAns e x.2.1 (encBot (Gamma ω g)), x.2.2)

/-- **`R^O_{c,e} = (S^O_{c,e})† U_Γ S^O_{c,e}`** (97), p.84: the coherent request of
`affine_{a_c,e}` from `Γ`, using the anchor `A`, the torch `T` and the CGS flame `K`. -/
noncomputable def Rce (ω : Sample lam R) (s : Serial lam) (t : Key lam) (c : Fin (L lam))
    (e : ZMod 2) : Matrix (RSpace lam) (RSpace lam) ℂ :=
  (Sprep ω s t c e)ᴴ * gammaQuery ω s t c e * Sprep ω s t c e

/-- **The ideal affine query `U_{affine_{a_c,e}}`** on the affine registers (App. C.2, p.84):
`|u⟩_X |z⟩_C ↦ |u⟩_X |z ⊕ affine_{a_c,e}(u)⟩_C` (answer with its ⊥ flag; `affine_{·,1}` is `⊥` off
`W_{a_c}`). -/
noncomputable def Uaff (ω : Sample lam R) (s : Serial lam) (c : Fin (L lam)) (e : ZMod 2) :
    Matrix (AffPair lam) (AffPair lam) ℂ :=
  basisMat fun p => writeAns e p (encBot (affineAns ω s c (affIn e p)))

/-- **The anchor signing error** `e_A = Σ_{c=1}^L Σ_{b=0}^1 ϵ_{a_c, b}` (50), p.54, with `ϵ_{y,b}` the
pointwise error of Theorem 4.10 in component `c` of `O_{A,ℓ}`. -/
noncomputable def eA (ω : Sample lam R) (s : Serial lam) : ℝ :=
  ∑ c, ∑ b : ZMod 2, signErr ((OA ω s.1).1 c) (s.2 c) b

/-- **The torch signing error** `e_T = Σ_{j=1}^R Σ_{c=1}^L Σ_{b=0}^1 ϵ_{t_{j,c}, b}` (50), p.54, in
`O_T`. -/
noncomputable def eT (ω : Sample lam R) : ℝ :=
  ∑ j, ∑ c, ∑ b : ZMod 2, signErr ((OT ω).1 c) (tk ω j c) b

/-- **The tag error** `e_tag` (51), p.54, for `O_K`.

**Formalization Note** (51) takes the supremum over unit vectors of `Z ⊗ E`. The quantity
`‖(I − Π) Fire.Tag(|K⟩ ⊗ |ψ⟩ ⊗ |0⟩)‖²` is a quadratic form `⟨ψ|(M_Z ⊗ I_E)|ψ⟩` in `ψ`, so its
supremum is the largest eigenvalue of `M_Z` for every nonempty `E`; it is taken here with `E`
trivial. -/
noncomputable def etag (ω : Sample lam R) : ℝ := CGS.tagErr (OK ω) Unit

/-- `d = min{1, e_A + e_T + e_tag}` (53), p.55. -/
noncomputable def dErr (ω : Sample lam R) (s : Serial lam) : ℝ :=
  min 1 (eA ω s + eT ω + etag ω)

/-- `e(λ) = 2^{−λ} + 2^{−(n−r)}` (Theorem 4.10, p.22; (50), p.54: `2^{−λ} + 2^{−24λ}`). -/
noncomputable def eLam (lam : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ eff lam + (2 : ℝ)⁻¹ ^ nr lam

end TorchFire.TF


