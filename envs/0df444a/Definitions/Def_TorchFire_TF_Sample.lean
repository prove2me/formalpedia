-- Prove2me | Definitions.Def_TorchFire_TF_Sample
-- name    : TorchFire_TF_Sample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:40:18.127196+00:00
-- url     : https://prove2.me/theorems/92236496-a15e-40ab-aadd-949f7d2455f1
-- title:
--   Torch-fire oracles: $O_T$, $(O_{A,\ell})_\ell$, $O_K$, torch keys, $T$ (36), messages (43), $\mathrm{code}$ (44), $\Gamma$ (45)–(46), $\Gamma^0_i$ (85), (47), witnesses (86)
-- statement:
--   The oracle layer of Construction 7.4 with $L=\lambda$, the OSS parameters at $\lambda$, and CGS fire at $\mu=\lambda^2$ (p.47).
--
--   1. **$\mathrm{TF.GenOracles}(1^\lambda,1^R)$**: a long-message OSS collection $O_T$ for all torches, an independent one $O_{A,\ell}$ for every label $\ell\in\{0,1\}^\lambda$, a CGS collection $O_K$ (with its private $G,H_0,H_1,h$), and independent uniform torch keys $t_j\in(\{0,1\}^r)^L$, $j\in[R]$, published by $T(j)=t_j$ for $j\in[R]$ and $\perp$ otherwise (36); $T_{\mathrm{pub}}=\{t_j\}$.
--   2. Serials $s=(\ell,a)$ (38); the messages $M_A(s,t)=0\Vert\langle s,t\rangle$, $M_T(s,t)=1\Vert\langle s,t\rangle$ with $\langle s,t\rangle=\ell\Vert a_1\Vert\cdots\Vert a_L\Vert t_1\Vert\cdots\Vert t_L$ (43); $\mathrm{code}(q)=\langle s,t\rangle\Vert[c]_\lambda\Vert e\Vert u\Vert0\cdots0$ and $z_q=\mathrm{enc}(\mathrm{forward},\mathrm{code}(q))$ (44).
--   3. The affine maps $\mathrm{affine}_{y,0}(w)=A_yw+b_y$, $\mathrm{affine}_{y,1}(u)=w$ if $u=A_yw+b_y$, $\perp$ if $u\notin W_y$ (41).
--   4. **The $\Gamma$ oracle** (Construction 7.3): on $(q,p,\sigma_A,\sigma_T)$, $q=(s,t,c,e,u)$, it checks (45) — $q\in Q_{\mathrm{affine}}$, $t\in T_{\mathrm{pub}}$, $\mathrm{OSS.Ver}^{O_{A,\ell}}(a,M_A(s,t),\sigma_A)=1$, $\mathrm{OSS.Ver}^{O_T}(t,M_T(s,t),\sigma_T)=1$, $\mathrm{Fire.Check}(z_q,p)=1$ — and returns $\mathrm{affine}_{a_c,e}(u)$ in component $c$ of $O_{A,\ell}$ if they hold, $\perp$ otherwise (46).
--   5. **The full public collection** $O=(O_T,(O_{A,\ell})_\ell,O_K,T,\Gamma)$ (47), with $O_K$ the CGS public collection (26); and the modified collection with $\Gamma^0_i$, which is $\perp$ on every request carrying the label $\ell_i$ (85).
--   6. The **witness predicate** (86) and the diagonal witness projector $Q_i$ on the query register: $q'\in Q_{\mathrm{affine}}$ with label $\ell_i$, $t\in T_{\mathrm{pub}}$, and a valid torch signature on $M_T(s',t)$.
--
--   **Formalization Note** Oracle generation takes $R$ (paper.md decision 11). Torch indices are $0$-based; $T$'s domain is $\{0,\dots,R\}$ with $0\notin[R]$ answered $\perp$. Component indices $c$ are written $0$-based in $[c]_\lambda$; the encoding stays injective. $\Gamma$ reads $s,t,c,e$ and $u$ from its query input; malformed inputs return $\perp$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §7.1 pp.47–51: (36) p.48, (38)–(41) p.49, (43)–(44) pp.50–51, Construction 7.3 (45)–(46) p.51, (47) p.51; Construction 7.4 item 1 p.52; (85)–(86) p.70

import Mathlib
import Definitions.Def_TorchFire_OSS_LongSample
import Definitions.Def_TorchFire_CGS_Sample

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.TF

/-- The CGS security parameter `µ = λ²` of torch-fire (p.47), at the effective `λ`. -/
abbrev muK (lam : ℕ) : ℕ := eff lam ^ 2

/-- The length `1 + λ + 2Lr` of the signed messages `M_A(s, t)`, `M_T(s, t)` ((43), p.50). -/
abbrev lM (lam : ℕ) : ℕ := 1 + eff lam + 2 * L lam * r lam

/-- The message space of the torch and anchor long-message OSS: `{0,1}^{≤ 1+λ+2Lr}` (paper.md
decision 10). -/
abbrev Msg (lam : ℕ) : Type := BitStr (lM lam)

/-- An anchor label `ℓ ∈ {0,1}^λ` (p.48). -/
abbrev Label (lam : ℕ) : Type := Bits (eff lam)

/-- A long-message OSS verification key `(t_1, …, t_L) ∈ ({0,1}^r)^L` (a torch key or an anchor
key). -/
abbrev Key (lam : ℕ) : Type := Fin (L lam) → Bits (r lam)

/-- **A flame serial** `s = (ℓ, a)` (38), p.49. -/
abbrev Serial (lam : ℕ) : Type := Label lam × Key lam

/-- **The oracle and key distribution of `TF.GenOracles(1^λ, 1^R)`** (Construction 7.4 item 1,
p.52, with §7.1 pp.47–48; Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated
Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593): one long-message OSS collection
`O_T` for all torches (i); an independent long-message OSS collection `O_{A,ℓ}` for every label
`ℓ ∈ {0,1}^λ` (ii); a CGS fire collection `O_K` at `µ = λ²` including its private `G, H_0, H_1, h`
(iii); and independent uniform torch keys `t_j ∈ ({0,1}^r)^L`, `j ∈ [R]` (p.48). Uniform on the
product.

**Formalization Note** Oracle generation takes `R` (paper.md decision 11: Construction 7.4 item 1 is
`TF.GenOracles(1^λ, 1^R)`). Torch indices `j ∈ [R]` are `Fin R` (`0`-based). -/
abbrev Sample (lam R : ℕ) : Type :=
  LongSample lam (Msg lam) × (Label lam → LongSample lam (Msg lam)) × CGS.Sample (muK lam) ×
    (Fin R → Key lam)

noncomputable instance (lam R : ℕ) : Fintype (Sample lam R) := inferInstance

variable {lam R : ℕ}

/-- The torch source `O_T`. -/
def OT (ω : Sample lam R) : LongSample lam (Msg lam) := ω.1
/-- The anchor source `O_{A,ℓ}`. -/
def OA (ω : Sample lam R) (l : Label lam) : LongSample lam (Msg lam) := ω.2.1 l
/-- The CGS source `O_K`. -/
def OK (ω : Sample lam R) : CGS.Sample (muK lam) := ω.2.2.1
/-- The torch keys `t_1, …, t_R`. -/
def tk (ω : Sample lam R) : Fin R → Key lam := ω.2.2.2

/-- **The key oracle** `T(j) = t_j` for `j ∈ [R]`, `⊥` otherwise (36), p.48: the domain is
`{0, …, R}`, with `0 ∉ [R]` answered `⊥` and `j ≥ 1` answered `t_j`. -/
def Torc (ω : Sample lam R) (j : Fin (R + 1)) : Option (Key lam) :=
  if h : 0 < j.val then some (tk ω ⟨j.val - 1, by omega⟩) else none

/-- `t ∈ T_pub = {t_j : j ∈ [R]}` (36). -/
def InTpub (ω : Sample lam R) (t : Key lam) : Prop := ∃ j, tk ω j = t

noncomputable instance (ω : Sample lam R) (t : Key lam) : Decidable (InTpub ω t) :=
  Classical.dec _

/-- `⟨s, t⟩ = ℓ ∥ a_1 ∥ ⋯ ∥ a_L ∥ t_1 ∥ ⋯ ∥ t_L` (43), p.50, as a bit list. -/
def pairBits (s : Serial lam) (t : Key lam) : List (ZMod 2) :=
  bitsToList s.1 ++ (List.ofFn fun c => bitsToList (s.2 c)).flatten ++
    (List.ofFn fun c => bitsToList (t c)).flatten

/-- A bit list as an element of `{0,1}^{≤ 1+λ+2Lr}` (the lists used here have exactly that length). -/
def toMsg (l : List (ZMod 2)) : Msg lam :=
  ⟨⟨min l.length (lM lam), Nat.lt_succ_of_le (min_le_right _ _)⟩, fun i => l.getD i.val 0⟩

/-- `M_A(s, t) = 0 ∥ ⟨s, t⟩` (43), p.50: the message signed by the anchor. -/
def msgA (s : Serial lam) (t : Key lam) : Msg lam := toMsg (0 :: pairBits s t)

/-- `M_T(s, t) = 1 ∥ ⟨s, t⟩` (43), p.50: the message signed by the torch. -/
def msgT (s : Serial lam) (t : Key lam) : Msg lam := toMsg (1 :: pairBits s t)

/-- The affine input `u`: `n − r` bits for `e = 0`, `k` bits for `e = 1` (p.50). -/
abbrev AffIn (lam : ℕ) : Type := Bits (nr lam) ⊕ Bits (k lam)

/-- **A `Γ` query input** `(q, p, σ_A, σ_T)` with `q = (s, t, c, e, u)` (Construction 7.3, p.51):
the serial `s`, the torch key `t`, the component `c ∈ [L]`, the bit `e`, the affine input `u`, a CGS
tag `p` (as held in registers, with ⊥ flags) and two long-message signatures. -/
abbrev GammaDom (lam : ℕ) : Type :=
  Serial lam × Key lam × Fin (L lam) × ZMod 2 × AffIn lam × CGS.TagIn (muK lam) ×
    (Fin (L lam) → Sig lam) × (Fin (L lam) → Sig lam)

/-- The `Γ` answer: `affine_{a_c,0}(u) ∈ {0,1}^k` in the first slot, `affine_{a_c,1}(u) ∈ {0,1}^{n−r}` in
the second (zero-padded). -/
abbrev GammaAns (lam : ℕ) : Type := Bits (k lam) × Bits (nr lam)

instance (lam : ℕ) : Fintype (GammaDom lam) := inferInstance
instance (lam : ℕ) : DecidableEq (GammaDom lam) := inferInstance
instance (lam : ℕ) : Fintype (GammaAns lam) := inferInstance
instance (lam : ℕ) : DecidableEq (GammaAns lam) := inferInstance

/-- `q = (s, t, c, e, u) ∈ Q_affine`: the length of `u` matches `e` (p.50). -/
def WellFormed (g : GammaDom lam) : Prop :=
  (g.2.2.2.1 = 0 ∧ g.2.2.2.2.1.isLeft = true) ∨ (g.2.2.2.1 = 1 ∧ g.2.2.2.2.1.isRight = true)

noncomputable instance (g : GammaDom lam) : Decidable (WellFormed g) := Classical.dec _

/-- The bits of the affine input. -/
def affBits : AffIn lam → List (ZMod 2)
  | .inl w => bitsToList w
  | .inr u => bitsToList u

/-- **`code(q) = ⟨s, t⟩ ∥ [c]_λ ∥ e ∥ u ∥ 0⋯0 ∈ {0,1}^{n_K}`** (44), pp.50–51, and
`z_q = enc(forward, code(q))` (p.51), with the CGS encoding (21) of `O_K`. -/
def zq (s : Serial lam) (t : Key lam) (c : Fin (L lam)) (e : ZMod 2) (u : AffIn lam) :
    Bits (CGS.ell (muK lam)) :=
  CGS.enc (.forward (listToBits _ (pairBits s t ++ bitsToList (natToBits (eff lam) c.val) ++
    [e] ++ affBits u)))

/-- `affine_{y,0}(w) = A_y w + b_y` (41), p.49, in one anchor component. -/
def affine0 (ω1 : OneSample lam) (y : Bits (r lam)) (w : Bits (nr lam)) : Bits (k lam) :=
  (Amat ω1 y).mulVec w + bvec ω1 y

/-- `affine_{y,1}(u) = w` if `u = A_y w + b_y`, `⊥` if `u ∉ W_y` (41), p.49 (`w` unique by full column
rank). -/
noncomputable def affine1 (ω1 : OneSample lam) (y : Bits (r lam)) (u : Bits (k lam)) :
    Option (Bits (nr lam)) :=
  by classical exact if h : InCoset ω1 y u then some (Classical.choose h) else none

/-- The affine answer `affine_{a_c,e}(u)` of component `c` of `O_{A,ℓ}`, in `Γ`'s answer slots. -/
noncomputable def affineAns (ω : Sample lam R) (s : Serial lam) (c : Fin (L lam)) :
    AffIn lam → Option (GammaAns lam)
  | .inl w => some (affine0 ((OA ω s.1).1 c) (s.2 c) w, 0)
  | .inr u => (affine1 ((OA ω s.1).1 c) (s.2 c) u).map fun w => (0, w)

/-- **The checks (45)** of `Γ` (Construction 7.3, p.51): `q ∈ Q_affine`, `t ∈ T_pub`, the anchor
signature verifies on `M_A(s, t)` under `a` in `O_{A,ℓ}`, the torch signature verifies on `M_T(s, t)`
under `t` in `O_T`, and `Fire.Check(z_q, p) = 1` in `O_K`. -/
def GammaChecks (ω : Sample lam R) (g : GammaDom lam) : Prop :=
  WellFormed g ∧ InTpub ω g.2.1 ∧
    longVer (OA ω g.1.1) g.1.2 (msgA g.1 g.2.1) g.2.2.2.2.2.2.1 ∧
    longVer (OT ω) g.2.1 (msgT g.1 g.2.1) g.2.2.2.2.2.2.2 ∧
    CGS.checkIn (OK ω) (zq g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1) g.2.2.2.2.2.1

noncomputable instance (ω : Sample lam R) (g : GammaDom lam) : Decidable (GammaChecks ω g) :=
  Classical.dec _

/-- **The `Γ` oracle** (46), Construction 7.3, p.51: `affine_{a_c,e}(u)` if (45) holds, `⊥` otherwise
(malformed inputs return `⊥`). -/
noncomputable def Gamma (ω : Sample lam R) (g : GammaDom lam) : Option (GammaAns lam) :=
  if GammaChecks ω g then affineAns ω g.1 g.2.2.1 g.2.2.2.2.1 else none

/-- **`Γ⁰_i`** (85), p.70: `⊥` on every request carrying the label `ℓ_i`, `Γ` otherwise. -/
noncomputable def Gamma0 (ω : Sample lam R) (li : Label lam) (g : GammaDom lam) :
    Option (GammaAns lam) :=
  if g.1.1 = li then none else Gamma ω g

/-- The query domain of the full public collection (47). -/
abbrev PubDom (lam R : ℕ) : Type :=
  LongDom lam (Msg lam) ⊕ (Label lam × LongDom lam (Msg lam)) ⊕ CGS.PubDom (muK lam) ⊕
    Fin (R + 1) ⊕ GammaDom lam

/-- Its answer register. -/
abbrev PubAns (lam : ℕ) : Type :=
  LongAns lam × LongAns lam × CGS.PubAns (muK lam) × (ZMod 2 × Key lam) × (ZMod 2 × GammaAns lam)

instance (lam R : ℕ) : Fintype (PubDom lam R) := inferInstance
instance (lam R : ℕ) : DecidableEq (PubDom lam R) := inferInstance
instance (lam : ℕ) : Fintype (PubAns lam) := inferInstance
instance (lam : ℕ) : DecidableEq (PubAns lam) := inferInstance

/-- The public collection with a given gatekeeping oracle in place of `Γ`. -/
noncomputable def pubOracleWith (ω : Sample lam R) (γ : GammaDom lam → Option (GammaAns lam)) :
    PubDom lam R → PubAns lam :=
  combine (longPubOracle (OT ω)) <| combine (indexed fun l => longPubOracle (OA ω l)) <|
    combine (CGS.pubOracle (OK ω)) <| combine (fun j => encBot (Torc ω j)) (fun g => encBot (γ g))

/-- **The full public oracle collection** `O = (O_T, (O_{A,ℓ})_ℓ, O_K, T, Γ)` (47), p.51, where `O_K`
is the CGS public collection (26). `G`, `td_T`, `H_0, H_1, h`, `D_0` and the affine maps are reachable
only through these oracles. -/
noncomputable def pubOracle (ω : Sample lam R) : PubDom lam R → PubAns lam :=
  pubOracleWith ω (Gamma ω)

/-- **The modified collection `O⁰_i`** (p.70): `Γ` replaced by `Γ⁰_i` for the label `ℓ_i`. -/
noncomputable def modOracle (ω : Sample lam R) (li : Label lam) : PubDom lam R → PubAns lam :=
  pubOracleWith ω (Gamma0 ω li)

/-- **The witness predicate (86)**, p.70: a complete `Γ`-query input with `q′ = (s′, t, c, e, u) ∈
Q_affine`, `s′ = (ℓ_i, a′)`, `t ∈ T_pub`, and `OSS.Ver^{O_T}(t, M_T(s′, t), σ_T) = 1`; false on every
other query (malformed inputs, other components). -/
def IsWitness (ω : Sample lam R) (li : Label lam) : PubDom lam R → Prop
  | .inr (.inr (.inr (.inr g))) =>
    WellFormed g ∧ g.1.1 = li ∧ InTpub ω g.2.1 ∧
      longVer (OT ω) g.2.1 (msgT g.1 g.2.1) g.2.2.2.2.2.2.2
  | _ => False

noncomputable instance (ω : Sample lam R) (li : Label lam) (x : PubDom lam R) :
    Decidable (IsWitness ω li x) := Classical.dec _

/-- **The witness projector `Q_i`** of §8.2 on the query and answer registers of the public
collection: the computational-basis diagonal projector onto the query inputs satisfying (86). -/
noncomputable def witnessProj (ω : Sample lam R) (li : Label lam) :
    Matrix (PubDom lam R × PubAns lam) (PubDom lam R × PubAns lam) ℂ :=
  Matrix.diagonal fun x => if IsWitness ω li x.1 then 1 else 0

end TorchFire.TF


