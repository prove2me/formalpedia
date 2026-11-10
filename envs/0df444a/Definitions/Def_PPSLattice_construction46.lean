-- Prove2me | Definitions.Def_PPSLattice_construction46
-- name    : PPSLattice_construction46
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:37:37.59336+00:00
-- url     : https://prove2.me/theorems/0c9c8e9c-a398-4458-ab95-b0699885e4cf
-- title:
--   Construction 4.6: the PPS scheme from SEPRF, blind garbling and LWE
-- statement:
--   For parameters $P$, a compiler $K$ for Figure 1 with size $s_C$, homomorphic computation algorithms, an SEPRF scheme and a garbling scheme, with $m=n\lceil\log q\rceil$ and $L=L_{\tilde C}$:
--
--   - $\mathrm{GSetup}(1^\lambda,N)$: $\mathbf A\leftarrow\mathbb Z_q^{n\times(\lceil\log N\rceil m)}$, $\mathrm{crs}:=\mathbf A$.
--   - $\mathrm{MSKGen}$: $\mathrm{prf.key}\leftarrow\mathrm{SEPRF.Setup}(1^\lambda,1^L)$, $\mathrm{garb.gk}\leftarrow\mathrm{Garb.Setup}(1^\lambda,1^{s_C},1^{nm\lceil\log q\rceil})$.
--   - $\mathrm{pkEnc}(i)$: $t\leftarrow\{0,1\}^\lambda$, $T\leftarrow\{0,1\}^L$.
--   - $\mathrm{KGen}(\mathrm{msk},S)$: $\mathbf A_S=\mathrm{EvalF}(\mathbf A,f_S)$, $\mathrm{sk}_S:=(\mathrm{prf.key},\mathrm{Garb.InpGarb}(\mathrm{garb.gk},\mathbf A_S))$.
--   - $\mathrm{skEnc}(\mathrm{msk},i,\mu)$: $\mathbf s\leftarrow\mathbb Z_q^n$, $\mathbf e\leftarrow D^{\lceil\log N\rceil m}_{\mathbb Z,\chi}$, $\mathbf P\leftarrow\mathbb Z_q^{n\times\lambda}$, $\tilde{\mathbf e}\leftarrow[-\sqrt m\tilde\chi,\sqrt m\tilde\chi]^\lambda$, $tg$ as in `tgLaw`, the randomness of Remark 4.9; $\tilde C\leftarrow\mathrm{Garb.CircGarb}(\mathrm{garb.gk},C)$ for the circuit $C$ of Figure 1; $t\leftarrow\{0,1\}^\lambda$, $T=\mathrm{SEPRF.Eval}(\mathrm{prf.key},t)\oplus\tilde C$.
--   - $\mathrm{Decode}(S,\mathrm{sk}_S,i,\mathrm{ct})$: $\perp$ if $i\notin S$; else $\tilde C=T\oplus\mathrm{SEPRF.Eval}(\mathrm{prf.key},t)$, $(\mathbf c^\top,\mathbf P,\mathbf d^\top,h)=\mathrm{Garb.Eval}(\tilde C,\tilde{\mathbf A}_S)$, $\mathbf H_{S,i}=\mathrm{EvalFX}(\mathbf A,f_S,\mathrm{encvec}(i))$, $tg'=\mathbf d^\top-\mathbf c^\top\mathbf H_{S,i}\mathbf G^{-1}(\mathbf P)$, output $h\oplus\lceil tg'\rfloor_2$.
--
--   **Formalization Note** Defined at the level of distributions, as printed, with an exact discrete Gaussian; it is not claimed efficient, and its perfect correctness is not claimed (an unbounded Gaussian error can flip a decoded bit). The interval of $\tilde{\mathbf e}$ is $[-\lfloor\sqrt m\tilde\chi\rfloor,\lfloor\sqrt m\tilde\chi\rfloor]$; one encoding randomness $r_j$ per element of $\mathbb Z_q$ (Remark 4.9).
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21; Figure 1 and Remark 4.9, p.22

import Mathlib
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_PPSLattice_Params
import Definitions.Def_PPSLattice_HomEval
import Definitions.Def_PPSLattice_SEPRF
import Definitions.Def_PPSLattice_Garb
import Definitions.Def_PPSLattice_memCircuit
import Definitions.Def_PPSLattice_figCode
import Definitions.Def_PPSLattice_tgLaw
import Definitions.Def_PPSLattice_unifInt
import Definitions.Def_PPSLattice_uniformMat
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_PPSLattice_dGaussZq
import Definitions.Def_PPSLattice_decMat
import Definitions.Def_PPSLattice_encvec
import Definitions.Def_PPSLattice_gadgetInv
import Definitions.Def_PPSLattice_round2
import Definitions.Def_PPSLattice_xorStr
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The input length `n · m · ⌈log q⌉` of the circuit of Figure 1. -/
def c46InLen (P : Params) (lam N : ℕ) : ℕ :=
  P.n lam N * P.m lam N * Nat.clog 2 (P.q lam N)

/-- The output length of the circuit of Figure 1: `(⌈log N⌉m + nλ + λ)` elements of `Z_q` in `ℓ_q = ⌈log q⌉ + λ`
bits each, then `λ` bits. -/
def c46OutLen (P : Params) (lam N : ℕ) : ℕ :=
  (Nat.clog 2 N * P.m lam N + P.n lam N * lam + lam) * (Nat.clog 2 (P.q lam N) + lam) + lam

/-- The garbled-circuit length `L_C̃`. -/
def c46L (P : Params) (sC : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Garb) (lam N : ℕ) : ℕ :=
  G.glen lam (sC lam N (P.n lam N) (P.q lam N)) (c46InLen P lam N) (c46OutLen P lam N)

/-- **Construction 4.6**: the PPS scheme for `M_λ = {0,1}^λ` built from the parameters `P`, a circuit
compiler `K` for Figure 1 with size function `s_C`, the homomorphic computation algorithms `H`, an SEPRF
scheme `F` and a blind garbling scheme `G`. With `n, q, χ, χ̃, B` the values of `P` at `(λ, N)`, `m = n⌈log q⌉`,
`L = L_C̃`:
- `GSetup(1^λ, N)`: `A ← Z_q^{n×(⌈log N⌉·m)}`; `crs := A`.
- `MSKGen`: `prf.key ← SEPRF.Setup(1^λ, 1^{L})`, `garb.gk ← Garb.Setup(1^λ, 1^{s_C}, 1^{n·m·⌈log q⌉})`;
  `msk := (prf.key, garb.gk)`.
- `pkEnc(i)`: `t ← {0,1}^λ`, `T ← {0,1}^L`; `ct := (t, T)`.
- `KGen(msk, S)`: `A_S = EvalF(A, f_S)`, `Ã_S = Garb.InpGarb(garb.gk, A_S)`; `sk_S := (prf.key, Ã_S)`.
- `skEnc(msk, i, µ)`: `s ← Z_q^n`, `e ← D^{⌈log N⌉·m}_{Z,χ}`, `P ← Z_q^{n×λ}`, `ẽ ← [−√m χ̃, √m χ̃]^λ`, `tg` as in
  `tgLaw`, the encoding randomness of Remark 4.9; `C̃ ← Garb.CircGarb(garb.gk, C)` for the circuit `C` of
  Figure 1 (compiled by `K`); `t ← {0,1}^λ`, `T = SEPRF.Eval(prf.key, t) ⊕ C̃`; `ct := (t, T)`.
- `Decode(S, sk_S, i, ct)`: `⊥` if `i ∉ S`; otherwise `C̃ = T ⊕ SEPRF.Eval(prf.key, t)`,
  `(c^⊤, P, d^⊤, h) = Garb.Eval(C̃, Ã_S)` (parsed as in Remark 4.9, reduced modulo `q`),
  `H_{S,i} = EvalFX(A, f_S, encvec(i))`, `tg′ = d^⊤ − c^⊤H_{S,i}G^{-1}(P)`; output `µ′ := h ⊕ ⌈tg′⌋₂`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21 (quoted in full: "Construction 4.6. We provide the construction of a PPS
scheme for M_λ = {0,1}^λ using an SEPRF scheme (Definition 4.2) and a blind garble circuit scheme Garb
(Definition 4.4), and relying on the LWE assumption (Assumption 3.4) below. GSetup(1^λ, N). Sample matrix
A ← Z_q^{n×(⌈log N⌉·m)}. Output crs := A. MSKGen. Sample prf.key ← SEPRF.Setup(1^λ, 1^{L_C̃}) and
garb.gk ← Garb.Setup(1^λ, 1^{s_C}, 1^{n·m·⌈log q⌉}). … pkEnc(i). Given i ∈ [N], sample t ← {0,1}^λ,
T ← {0,1}^{L_C̃}. Output ct := (t, T). KGen(msk, S). … skEnc(msk, i, µ). … Decode(S, sk_S, i, ct). …
Output µ′ := h ⊕ ⌈tg′⌋₂."); Figure 1 and Remark 4.9, p.22.

**Formalization Note.** The construction is defined at the level of distributions, exactly as printed,
with an exact discrete Gaussian; it is not claimed to be efficient. Pairs are coded with `tup`, matrices
and vectors with `encMat`/`encVec`. The interval for `ẽ` is `[−⌊√m·χ̃⌋, ⌊√m·χ̃⌋]`. The encoding randomness
is one `r_j ← [0, ⌊2^{ℓ_q}/q⌋ − 1]` per element of `Z_q` in the output of Figure 1 (see `figOut`). -/
noncomputable def construction46 (P : Params) (K : Str → RestrictedDec.Circuit)
    (sC : ℕ → ℕ → ℕ → ℕ → ℕ) (H : HomEval) (F : SEPRF) (G : Garb) : PPS where
  gsetup lam N :=
    (uniformMat (P.q lam N) (P.n lam N) (Nat.clog 2 N * P.m lam N)).map (encMat (P.q lam N))
  mskgen lam N _ :=
    (F.setup lam (c46L P sC G lam N)).bind fun key =>
      (G.setup lam (sC lam N (P.n lam N) (P.q lam N)) (c46InLen P lam N)).map fun gk =>
        BeyondDS.tup [key, gk]
  pkEnc lam N _ _ :=
    (AvgPHETH.uniformDist lam).bind fun t =>
      (AvgPHETH.uniformDist (c46L P sC G lam N)).map fun T => BeyondDS.tup [t, T]
  kgen lam N crs msk S :=
    let A := decMat (P.q lam N) (P.n lam N) (Nat.clog 2 N * P.m lam N) crs
    let AS := H.evalF (P.q lam N) (P.n lam N) (P.m lam N) (Nat.clog 2 N) A (memCircuit N S)
    PMF.pure (BeyondDS.tup [(BeyondDS.untup msk).getD 0 [],
      G.inpGarb ((BeyondDS.untup msk).getD 1 []) (encMat (P.q lam N) AS)])
  skEnc lam N crs msk i mu :=
    let q := P.q lam N
    let n := P.n lam N
    let A := decMat q n (Nat.clog 2 N * P.m lam N) crs
    let key := (BeyondDS.untup msk).getD 0 []
    let gk := (BeyondDS.untup msk).getD 1 []
    let ellq := Nat.clog 2 q + lam
    (iidVec (uniformZq q) n).bind fun s =>
    (iidVec (dGaussZq q (P.chi lam N)) (Nat.clog 2 N * P.m lam N)).bind fun e =>
    (uniformMat q n lam).bind fun Pm =>
    (iidVec ((unifInt ⌊Real.sqrt (P.m lam N) * P.chit lam N⌋₊).map fun z : ℤ => (z : ZMod q))
        lam).bind fun et =>
    (iidVec (tgLaw q (P.B lam N)) lam).bind fun tg =>
    (iidVec (MinSumClust.unifOr (Finset.range (2 ^ ellq / q)) 0)
        (Nat.clog 2 N * P.m lam N + n * lam + lam)).bind fun r =>
    (G.circGarb gk (K (figCode lam N n q A s e Pm et tg i mu (List.ofFn r)))).bind fun Ct =>
    (AvgPHETH.uniformDist lam).map fun t => BeyondDS.tup [t, xorStr (F.eval key t) Ct]
  decode lam N crs S sk i ct :=
    if i ∈ S then
      let q := P.q lam N
      let n := P.n lam N
      let m := P.m lam N
      let ellq := Nat.clog 2 q + lam
      let A := decMat q n (Nat.clog 2 N * m) crs
      let key := (BeyondDS.untup sk).getD 0 []
      let AS := (BeyondDS.untup sk).getD 1 []
      let t := (BeyondDS.untup ct).getD 0 []
      let T := (BeyondDS.untup ct).getD 1 []
      let out := G.eval (xorStr T (F.eval key t)) AS
      let c := decVec q ellq (Nat.clog 2 N * m) out
      let Pm : Matrix (Fin n) (Fin lam) (ZMod q) := Matrix.of fun a j =>
        decVec q ellq (n * lam) (out.drop (Nat.clog 2 N * m * ellq)) (finProdFinEquiv (a, j))
      let d := decVec q ellq lam (out.drop ((Nat.clog 2 N * m + n * lam) * ellq))
      let h := (out.drop ((Nat.clog 2 N * m + n * lam + lam) * ellq)).take lam
      let HS := H.evalFX q n m (Nat.clog 2 N) A (memCircuit N S) (encvec N i)
      let tg' : Fin lam → ZMod q := fun j => d j - ∑ a, c a * (HS * gadgetInv q n m Pm) a j
      some (xorStr h (List.ofFn fun j => round2 (tg' j)))
    else none

end PPSLattice


