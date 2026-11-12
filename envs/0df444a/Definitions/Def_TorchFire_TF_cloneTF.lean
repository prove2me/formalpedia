-- Prove2me | Definitions.Def_TorchFire_TF_cloneTF
-- name    : TorchFire_TF_cloneTF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:45:53.660035+00:00
-- url     : https://prove2.me/theorems/4cd3c1c7-1ba6-466e-a0a2-bce9e4befa49
-- title:
--   Torch-fire Setup, Spark, Ver and Clone of Construction 7.4
-- statement:
--   The honest procedures of **Construction 7.4**, each from its circuit.
--
--   1. **Torches** (step 2 (iii)): $T_j=\bigotimes_cT_{j,c}$, each prepared by circuit (42) — $H^{\otimes(n-r)}$ on $X$, $\mathrm{affine}_{y,0}:X\to Y$, $\mathrm{affine}_{y,1}:Y\to X$ — for $y=t_{j,c}$ from the authority's data $td_T$. **Setup aborts** iff two torch keys coincide.
--   2. **$\mathrm{TF.Spark}^O(sk)$** (step 3): sample $\ell\leftarrow\{0,1\}^\lambda$, run $\mathrm{OSS.GenQKey}^{O_{A,\ell}}$ (key $a$, anchor $A$), prepare $K$ by $\mathrm{Fire.Gen}^G$; output $s=(\ell,a)$ and $F=AK$ (a classical–quantum state).
--   3. **$\mathrm{TF.Ver}^O(pk,s,F)$** (step 4): the coset test of Lemma 4.8 in every anchor component under $a$ in $O_{A,\ell}$, then $\mathrm{Fire.Ver}^{O_K}(0^\mu,0^\mu,K)$; its accepting effect is the tensor product of the two procedures' effects ((48): $\Pi_a\otimes B$).
--   4. **$\mathrm{TF.Clone}^O(pk,t,s,T,F)$** (step 5): if $t\notin T_{\mathrm{pub}}$ return zero registers; otherwise run $\mathrm{Fire.Clone}^{O_K}(0^\mu,0^\mu,K)\to(K_0,K_1)$, then for each $c\in[L]$ apply $H^{\otimes(n-r)}$ to a fresh $X_c$, $R^O_{c,0}:X_c\to Y_c$ and $R^O_{c,1}:Y_c\to X_c$ using $A,T,K_0$, each affine call with fresh auxiliary registers; return $F_0=AK_0$, $T'=T$, $F_1=Y_1\cdots Y_LK_1$.
--
--   The CGS public key and serial inside torch-fire are $0^\mu$ (p.52).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 7.4 steps 2–5 pp.52–53; (42) p.50; (48) p.53

import Mathlib
import Definitions.Def_TorchFire_TF_Rce
import Definitions.Def_TorchFire_CGS_verEffect

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- **A torch-fire flame register** `F = AK` (40), p.49: the anchor `A = A_1 ⋯ A_L` and the CGS
flame part `K = YU`. -/
abbrev Flame (lam : ℕ) : Type := AReg lam × CGS.KReg (muK lam)

instance (lam : ℕ) : Fintype (Flame lam) := inferInstance
instance (lam : ℕ) : DecidableEq (Flame lam) := inferInstance

variable {lam R : ℕ}

/-- **The coset-state preparation circuit (42)**, p.50, from the private data `A_y, b_y` of one
component: `H^{⊗(n−r)}` on `X`, then `affine_{y,0} : X → Y`, then `affine_{y,1} : Y → X`; the output is
the state of `Y` (`X` returns to `|0⟩` and is discarded). -/
noncomputable def prep42 (ω1 : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  let U : Matrix (Bits (nr lam) × Bits (k lam)) (Bits (nr lam) × Bits (k lam)) ℂ :=
    basisMat (fun p => (p.1 + (affine1 ω1 y p.2).getD 0, p.2)) *
    basisMat (fun p => (p.1, p.2 + affine0 ω1 y p.1)) *
    hadOn (fun p : Bits (nr lam) × Bits (k lam) => (p.1, p.2))
  traceOutVia (fun p : Bits (k lam) × Bits (nr lam) => (p.2, p.1))
    (ketbra (U.mulVec (ket (0, 0))))

/-- **The torch `T_j`** prepared by `TF.Setup` (Construction 7.4 step 2 (iii), p.52): for every
`c ∈ [L]`, circuit (42) for `y = t_{j,c}` in component `c` of `O_T`, using `td_T`. -/
noncomputable def torchState (ω : Sample lam R) (j : Fin R) : Matrix (AReg lam) (AReg lam) ℂ :=
  piKron fun c => prep42 ((OT ω).1 c) (tk ω j c)

/-- `TF.Setup` does not abort: the published torch keys are pairwise distinct (Construction 7.4
step 2 (ii), p.52: "Abort if two keys coincide"). -/
def SetupOK (ω : Sample lam R) : Prop := Function.Injective (tk ω)

noncomputable instance (ω : Sample lam R) : Decidable (SetupOK ω) := Classical.dec _

/-- The torches `(T_j)_{j ∈ J}` handed out for a set `J ⊆ [R]` of size `m`, in increasing order of
`j`. -/
noncomputable def torchesOf (ω : Sample lam R) {m : ℕ} (J : Finset (Fin R)) (h : J.card = m) :
    Matrix (Fin m → AReg lam) (Fin m → AReg lam) ℂ :=
  piKron fun i => torchState ω (J.orderEmbOfFin h i)

/-- **`TF.Spark^O(sk)`** (Construction 7.4 step 3, p.52) as a cq-state on (serial `s = (ℓ, a)`) ×
(flame `F = AK`): sample `ℓ ← {0,1}^λ`; run `OSS.GenQKey^{O_{A,ℓ}}` (Construction 4.6 in every anchor
component, `Y` measured) to get the key `a` and the anchor `A`; prepare `K` by `Fire.Gen^G` (23) with
the authority's private access to `G`. -/
noncomputable def sparkCQ (ω : Sample lam R) :
    Matrix (Serial lam × Flame lam) (Serial lam × Flame lam) ℂ :=
  Matrix.of fun x y =>
    if x.1.1 = y.1.1 then
      (Fintype.card (Label lam) : ℂ)⁻¹ * longGenQKeyCQ (OA ω x.1.1) (x.1.2, x.2.1) (y.1.2, y.2.1) *
        CGS.flame (OK ω) x.2.2 y.2.2
    else 0

/-- **The accepting effect of `TF.Ver^O(pk, s, ·)`** (Construction 7.4 step 4, pp.52–53): the
anchor test of Lemma 4.8 / Remark 4.9 in every component of `A` under `a` in `O_{A,ℓ}`, followed by
`Fire.Ver^{O_K}(0^µ, 0^µ, K)`. The two tests act on disjoint registers, so the joint accepting effect
is the tensor product of the two procedures' accepting effects (the paper's (48), `Π_a ⊗ B`, follows
by Lemma 4.8). -/
noncomputable def verEff (ω : Sample lam R) (s : Serial lam) : Matrix (Flame lam) (Flame lam) ℂ :=
  Matrix.of fun x y =>
    longTestEffect (OA ω s.1) s.2 x.1 y.1 * CGS.verEffectKey (OK ω) 0 0 x.2 y.2

/-- The registers of `TF.Clone^O`: the torch `T`, the anchor `A`, the CGS clone registers (input flame
part `K`, its workspace, and the new `K_1` inside), the affine registers `X_c, Y_c` (and answer flags)
of every component, and the fresh auxiliary registers of the `2L` affine calls. -/
abbrev CloneSpace (lam : ℕ) : Type :=
  AReg lam × AReg lam × CGS.CloneSpace (muK lam) × (Fin (L lam) → AffPair lam) ×
    (Fin (L lam) → RWs lam × RWs lam)

instance (lam : ℕ) : Fintype (CloneSpace lam) := inferInstance
instance (lam : ℕ) : DecidableEq (CloneSpace lam) := inferInstance

/-- `R^O_{c,e}` acting on `A, T, K_0` and the registers of call `(c, e)` inside the clone registers. -/
noncomputable def RceOn (ω : Sample lam R) (s : Serial lam) (t : Key lam) (c : Fin (L lam))
    (e : ZMod 2) : Matrix (CloneSpace lam) (CloneSpace lam) ℂ :=
  liftOn (fun x : CloneSpace lam =>
      (((x.2.1, x.1, x.2.2.1.1), x.2.2.2.1 c,
          if e = 0 then (x.2.2.2.2 c).1 else (x.2.2.2.2 c).2),
        (x.2.2.1.2, Function.update x.2.2.2.1 c 0,
          Function.update x.2.2.2.2 c (if e = 0 then (rws0, (x.2.2.2.2 c).2)
            else ((x.2.2.2.2 c).1, rws0)))))
    (Rce ω s t c e)

/-- **The unitary of `TF.Clone^O(pk, t, s, T, F)`** for `t ∈ T_pub` (Construction 7.4 step 5,
p.53): (ii) `Fire.Clone^{O_K}(0^µ, 0^µ, K) → (K_0, K_1)`; (iii) for each `c ∈ [L]` in turn,
`H^{⊗(n−r)}` on `X_c`, `R^O_{c,0} : X_c → Y_c`, `R^O_{c,1} : Y_c → X_c` (the circuit (42) through `Γ`),
using `A, T, K_0`. -/
noncomputable def cloneU (ω : Sample lam R) (s : Serial lam) (t : Key lam) :
    Matrix (CloneSpace lam) (CloneSpace lam) ℂ :=
  let cgs := liftOn (fun x : CloneSpace lam => (x.2.2.1, (x.1, x.2.1, x.2.2.2))) (CGS.cloneU (OK ω))
  let step : Fin (L lam) → Matrix (CloneSpace lam) (CloneSpace lam) ℂ := fun c =>
    RceOn ω s t c 1 * RceOn ω s t c 0 *
      hadOn (fun x : CloneSpace lam =>
        ((x.2.2.2.1 c).1, (x.1, x.2.1, x.2.2.1, Function.update x.2.2.2.1 c 0, x.2.2.2.2,
          (x.2.2.2.1 c).2)))
  ((List.finRange (L lam)).map step).reverse.prod * cgs

/-- The discarded registers of `TF.Clone`: the CGS clone workspace (without `K_0`, `K_1`), the `X_c`
and flags, and the auxiliary registers of the affine calls. -/
abbrev CloneJunk (lam : ℕ) : Type :=
  ((Bits (CGS.ell (muK lam)) × CGS.TagWs (muK lam)) × (Bits (CGS.ell (muK lam)) × CGS.TagWs (muK lam)) ×
    (ZMod 2 × Bits (n (muK lam)) × ZMod 2) × (ZMod 2 × CGS.GAns (muK lam))) ×
  (Fin (L lam) → Bits (nr lam) × ZMod 2 × ZMod 2) × (Fin (L lam) → RWs lam × RWs lam)

instance (lam : ℕ) : Fintype (CloneJunk lam) := inferInstance
instance (lam : ℕ) : DecidableEq (CloneJunk lam) := inferInstance

/-- **`TF.Clone^O(pk, t, s, T, F)`** as a channel `TF ↦ F_0 (T′ F_1)` (Construction 7.4 step 5, p.53):
(i) if `t ∉ T_pub`, return zero registers of the prescribed sizes; otherwise embed `T`, `F = AK` and
fresh zero registers, apply `cloneU`, and return `F_0 = A K_0`, `T′ = T`, `F_1 = Y_1 ⋯ Y_L K_1`,
discarding the remaining workspace. (The output order `F_0`, then `(T′, F_1)`, is the one of the
cloning loop of (33): `F_0` is the returned copy, `(T′, F_1)` is cloned next.) -/
noncomputable def cloneTF (ω : Sample lam R) (t : Key lam) (s : Serial lam)
    (ρ : Matrix (AReg lam × Flame lam) (AReg lam × Flame lam) ℂ) :
    Matrix (Flame lam × (AReg lam × Flame lam)) (Flame lam × (AReg lam × Flame lam)) ℂ :=
  if InTpub ω t then
    let E : Matrix (CloneSpace lam) (AReg lam × Flame lam) ℂ :=
      basisMat fun x => (x.1, x.2.1, (x.2.2, CGS.cloneWs0), fun _ => 0, fun _ => (rws0, rws0))
    traceOutVia
      (fun p : (Flame lam × (AReg lam × Flame lam)) × CloneJunk lam =>
        (p.1.2.1, p.1.1.1,
          (p.1.1.2, p.2.1.1, p.2.1.2.1, (p.2.1.2.2.1.1, p.1.2.2.2, p.2.1.2.2.1.2), p.2.1.2.2.2),
          fun c => ((p.2.2.1 c).1, p.1.2.2.1 c, (p.2.2.1 c).2),
          p.2.2.2))
      (conjMat (cloneU ω s t) (conjMat E ρ))
  else Matrix.trace ρ • ketbra (ket (0, 0, 0))

end TorchFire.TF


