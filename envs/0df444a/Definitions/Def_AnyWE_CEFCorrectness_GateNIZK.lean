-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_GateNIZK
-- name    : AnyWE_CEFCorrectness_GateNIZK
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:52:05.396358+00:00
-- url     : https://prove2.me/theorems/d777f39b-fa06-4e37-a7a1-a98ec91b8e8e
-- title:
--   The gate-by-gate NIZK of Algorithm 1: $R_{\mathrm{gate}}$, $R^\vee_{\mathrm{gate}}$, $\Pi.\mathrm{Gen}$, $\Pi.P$, $\Pi.V$ and $R_{\mathrm{NIZK}}$ (fixed-length specialization)
-- statement:
--   Fix $\lambda$, the relation circuit $C=C_{n_x,n_w}$ (inputs $x\in\{0,1\}^{n_x}$ then $w\in\{0,1\}^{n_w}$, $g$ gates, $k=n_x+n_w+g$ wires), a commitment scheme $\mathrm{Com}$ and a length-doubling PRG $G$. The instance-input wires, the outputs of constant gates and the output wire are **public**; the others are **private**. A public wire is represented by its bit padded with zeros to $\ell_{com}$ bits (with the all-zero dummy opening), a private wire $a$ by $\gamma_a=\mathrm{Com}(\mathrm{crs}_{Com},\omega_a;r_a)$.
--
--   **$R_{\mathrm{gate}}$.** Instance $X=(i,\gamma_{i_1},\gamma_{i_2},\gamma_{i_3})$ ($i$ in binary), witness $\tau=(\omega_{i_1},\omega_{i_2},\omega_{i_3},r_{i_1},r_{i_2},r_{i_3})$: $i$ is a valid gate index, $\omega_{i_3}=g_i(\omega_{i_1},\omega_{i_2})$, each incident wire's representation is its padded bit (public) or the commitment with the given opening (private), and a repeated wire uses the same value and opening. **$R^\vee_{\mathrm{gate}}$** hardwires $\mathrm{crs}_{Com}$:
--   $$R^\vee_{\mathrm{gate}}\big((X,v),(d,u)\big)=1\iff(d=0\wedge R_{\mathrm{gate}}(X,u)=1)\vee(d=1\wedge G(u)=v),\qquad v\in\{0,1\}^{2\lambda},$$
--   with tagged, zero-padded witnesses.
--
--   **Algorithm 1**, with a NIWI for $R^\vee_{\mathrm{gate}}$:
--   - $\Pi.\mathrm{Gen}$: $\mathrm{crs}_{Com}\leftarrow\{0,1\}^{\ell_{crs}}$, $\mathrm{crs}_{NIWI}\leftarrow\mathrm{NIWI.Gen}(1^\lambda,R^\vee_{\mathrm{gate}}[\mathrm{crs}_{Com}])$, $v\leftarrow\{0,1\}^{2\lambda}$; $\mathrm{crs}=(\mathrm{crs}_{Com},\mathrm{crs}_{NIWI},v)$.
--   - $\Pi.P(\mathrm{crs},x,w)$: evaluate $C(x,w)$; represent every wire; for every gate $i$, $\pi_i\leftarrow\mathrm{NIWI}.P(\mathrm{crs}_{NIWI},(X_i,v),(0,\tau_i))$ with independent coins; output $(\gamma_1,\dots,\gamma_k,\pi_1,\dots,\pi_g)$.
--   - $\Pi.V(\mathrm{crs},x,\pi)$: the instance wires carry the bits of $x$, constant wires their constants, the output wire $1$, and $\mathrm{NIWI}.V$ accepts every $((X_i,v),\pi_i)$.
--
--   **$R_{\mathrm{NIZK}}$** (§7.2) has instance $(\mathrm{crs},x)$ and witness $\pi$: $R_{\mathrm{NIZK}}((\mathrm{crs},x),\pi)=1\iff\Pi.V(\mathrm{crs},x,\pi)=1$.
--
--   This NIZK is the tool that lets the decryptor of $\mathrm{WE}'$ turn a witness for $x$ into a witness for $(\mathrm{crs},x)$ in a way that can be simulated gate by gate.
--
--   **Formalization Note.** This is the fixed-length specialization (p. 52) with $N=n_w$, used by Corollary 7.6: the witness length, $N$ and the other setup parameters are constants of the circuits and are not written into the CRS, proofs or gate instances; at fixed lengths there are no malformed encodings. The prover's random tape has an opening for every wire (those of public wires are unused) and coins for every gate proof. The prover circuit omits its own check $R(x,w)=1$, which $\mathrm{WE}'.\mathrm{Dec}$ performs before calling it.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), pp. 52-53, §6.2 and Algorithm 1 (fixed-length specialization p. 52); p. 61, R_NIZK

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_Primitives
set_option autoImplicit false

/-!
# The gate-by-gate NIZK of Algorithm 1 (fixed-length specialization)

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), §6.2 pp. 52–53 (`R_gate`, `R^∨_gate`, Algorithm 1) and the
fixed-length specialization p. 52 ("When a witness length `n_w` is fixed in advance, we take
`N = n_w`"), used by Corollary 7.6 ("Take `N = n_w`", p. 64).

Throughout, `λ` is fixed, `C = RC λ` is the relation circuit `C_{n_x, n_w}` at instance length
`n_x = n λ` and witness length `n_w = m λ` (inputs `x` then `w`), with `g` gates and
`k = n_x + n_w + g` wires (wire `n_x + n_w + i` is the output of gate `i`). The public wires are
the instance inputs, the outputs of constant gates and the output wire; all other wires are
private. A public wire is represented by its bit padded with zeros to `ℓ_com` bits and has the
all-zero dummy opening; a private wire by a commitment. Gate indices are written in binary with
`Nat.size g` digits.
-/

namespace AnyWE.CEFCorrectness

namespace GateNIZK

variable (n m : ℕ → ℕ) (RC : ∀ lam, Circuit (n lam + m lam) 1) (Com : Commitment) (G : PRG)

/-- The number of gates `g` of `C_{n_x, n_w}`. -/
def numGates (lam : ℕ) : ℕ := (RC lam).gates.length

/-- The number of wires `k = n_x + n_w + g`. -/
def numWires (lam : ℕ) : ℕ := n lam + m lam + numGates n m RC lam

/-- The number of binary digits of a gate index. -/
def idxLen (lam : ℕ) : ℕ := Nat.size (numGates n m RC lam)

/-- Gate `i` of `C` (a constant-`0` gate if `i ≥ g`). -/
def gateAt (lam i : ℕ) : Gate := ((RC lam).gates[i]?).getD ⟨.const false, 0, 0⟩

/-- Whether wire `a` is public: an instance input, the output of a constant gate, or the output
wire. -/
def isPublic (lam a : ℕ) : Bool :=
  decide (a < n lam) ||
    (decide (n lam + m lam ≤ a) &&
      (match (RC lam).gates[a - (n lam + m lam)]? with
        | some ⟨.const _, _, _⟩ => true
        | _ => false)) ||
    decide (a = (RC lam).out 0)

/-- The padded representation `(c, 0, …, 0)` of a public bit. -/
def pad (len : ℕ) (c : Bool) : Bits len := fun j => decide (j.val = 0) && c

/-- The representation `γ_a` of wire `a` with value `ω` and opening `r`:
`ω` padded if `a` is public, `Com(crs_Com, ω; r)` if `a` is private. -/
def repr (lam a : ℕ) (crsCom : Bits (Com.crsLen lam)) (ω : Bool) (r : Bits (Com.randLen lam)) :
    Bits (Com.comLen lam) :=
  if isPublic n m RC lam a then pad (Com.comLen lam) ω else Com.commit lam crsCom ω r

/-- The length `3 + 3 ℓ_rand` of a gate witness `τ = (ω_{i1}, ω_{i2}, ω_{i3}, r_{i1}, r_{i2}, r_{i3})`. -/
def gateWitLen (lam : ℕ) : ℕ := 3 + Com.randLen lam + Com.randLen lam + Com.randLen lam

/-- **`R_gate` (p. 52)** on instance `X = (i, γ_{i1}, γ_{i2}, γ_{i3})` (the first part of an OR
instance) and witness `τ`: `i` is a valid gate index; `ω_{i3} = g_i(ω_{i1}, ω_{i2})`; each incident
wire's representation is its bit (public) or the commitment with its opening (private); and a wire
occurring twice uses the same value and opening. -/
def gateRel (lam : ℕ) (crsCom : Bits (Com.crsLen lam)) {L : ℕ} (X : Bits L)
    (τ : Bits (gateWitLen Com lam)) : Prop :=
  let ib := idxLen n m RC lam
  let lc := Com.comLen lam
  let lr := Com.randLen lam
  let i := (X.slice 0 ib).toNat
  let gt := gateAt n m RC lam i
  let ω₁ := τ.bitAt 0
  let ω₂ := τ.bitAt 1
  let ω₃ := τ.bitAt 2
  let r₁ := τ.slice 3 lr
  let r₂ := τ.slice (3 + lr) lr
  let r₃ := τ.slice (3 + lr + lr) lr
  i < numGates n m RC lam ∧
    gt.op.apply ω₁ ω₂ = ω₃ ∧
    (1 ≤ gt.op.arity → X.slice ib lc = repr n m RC Com lam gt.l crsCom ω₁ r₁) ∧
    (2 ≤ gt.op.arity → X.slice (ib + lc) lc = repr n m RC Com lam gt.r crsCom ω₂ r₂) ∧
    X.slice (ib + lc + lc) lc = repr n m RC Com lam (n lam + m lam + i) crsCom ω₃ r₃ ∧
    (2 ≤ gt.op.arity → gt.l = gt.r → ω₁ = ω₂ ∧ r₁ = r₂)

/-- **The OR relation `R^∨_gate` (p. 52)**, a relation family described by `crs_Com`: instance
`(X, v)` with `v ∈ {0,1}^{2λ}`, witness `(d, u)` (a tag bit and a zero-padded payload):
`(d = 0 ∧ R_gate(X, u) = 1) ∨ (d = 1 ∧ G(u) = v)`. -/
def orGateRel : NPRelFam where
  descLen := Com.crsLen
  instLen := fun lam => idxLen n m RC lam + Com.comLen lam + Com.comLen lam + Com.comLen lam + 2 * lam
  witLen := fun lam => 1 + max (gateWitLen Com lam) lam
  holds := fun lam crsCom Xv W =>
    let u := W.slice 1 (max (gateWitLen Com lam) lam)
    let v := Xv.slice (idxLen n m RC lam + Com.comLen lam + Com.comLen lam + Com.comLen lam) (2 * lam)
    (W.bitAt 0 = false ∧ (∀ j, gateWitLen Com lam ≤ j → u.bitAt j = false) ∧
        gateRel n m RC Com lam crsCom Xv (u.slice 0 (gateWitLen Com lam))) ∨
      (W.bitAt 0 = true ∧ (∀ j, lam ≤ j → u.bitAt j = false) ∧
        (G.G lam).eval (u.slice 0 lam) = v)

variable (NIWI : NIWIScheme (orGateRel n m RC Com G))

/-- The NIZK CRS `crs = (crs_Com, (crs_NIWI, v))`: length `ℓ_crs + |crs_NIWI| + 2λ`. -/
def crsLen (lam : ℕ) : ℕ := Com.crsLen lam + NIWI.crsLen lam + 2 * lam

/-- The random tape of `Π.Gen`: `crs_Com`'s coins, `NIWI.Gen`'s coins, and `v`. -/
def genTape (lam : ℕ) : ℕ := Com.crsLen lam + NIWI.genTape lam + 2 * lam

/-- The NIZK proof `(γ_1, …, γ_k, π_1, …, π_g)`. -/
def proofLen (lam : ℕ) : ℕ :=
  numWires n m RC lam * Com.comLen lam + numGates n m RC lam * NIWI.proofLen lam

/-- The random tape of `Π.P`: an opening for every wire (unused for public wires) and the coins
of every gate proof. -/
def proveTape (lam : ℕ) : ℕ :=
  numWires n m RC lam * Com.randLen lam + numGates n m RC lam * NIWI.proveTape lam

/-- **`Π.Gen(1^λ, n_x, n_w, R)` (Algorithm 1)**: `crs_Com ← Com.Gen(1^λ)` (uniform),
`crs_NIWI ← NIWI.Gen(1^λ, R^∨_gate[crs_Com])`, `v ← {0,1}^{2λ}`; output
`(crs_Com, crs_NIWI, v)`. -/
def gen (lam : ℕ) : Circuit (genTape n m RC Com G NIWI lam) (crsLen n m RC Com G NIWI lam) :=
  Circuit.build _ _ fun inp => do
    let crsCom := vleft (vleft inp)
    let crsN ← BM.embed (NIWI.gen lam) (Fin.append crsCom (vright (vleft inp)))
    pure (Fin.append (Fin.append crsCom crsN) (vright inp))

/-- The instance `(X_i, v) = ((i, γ_{i1}, γ_{i2}, γ_{i3}), v)` of gate `i`, from the wire
representations `γ` (wires `≥ k` are represented by zeros). -/
def gateInst (lam i : ℕ) (γ : ℕ → Bits (Com.comLen lam)) (v : Bits (2 * lam)) :
    Bits ((orGateRel n m RC Com G).instLen lam) :=
  Fin.append (Fin.append (Fin.append (Fin.append (binBits (idxLen n m RC lam) i)
    (γ (gateAt n m RC lam i).l)) (γ (gateAt n m RC lam i).r)) (γ (n lam + m lam + i))) v

/-- **`Π.V(crs, x, π)` (Algorithm 1)**: the public input wires carry the bits of `x`, constant
wires their constants, the output wire `1`, and `NIWI.V` accepts every gate proof. -/
def verify (lam : ℕ) (crs : Bits (crsLen n m RC Com G NIWI lam)) (x : Bits (n lam))
    (pf : Bits (proofLen n m RC Com G NIWI lam)) : Prop :=
  let γ : ℕ → Bits (Com.comLen lam) := fun a =>
    if h : a < numWires n m RC lam then
      fun j => (vleft pf) (finProdFinEquiv (⟨a, h⟩, j))
    else fun _ => false
  let crsN : Bits (NIWI.crsLen lam) := vright (vleft crs)
  let v : Bits (2 * lam) := vright crs
  (∀ i : Fin (n lam), γ i.val = pad (Com.comLen lam) (x i)) ∧
    (∀ (j : ℕ) (c : Bool) (l r : ℕ), (RC lam).gates[j]? = some ⟨.const c, l, r⟩ →
      γ (n lam + m lam + j) = pad (Com.comLen lam) c) ∧
    γ ((RC lam).out 0) = pad (Com.comLen lam) true ∧
    ∀ i : Fin (numGates n m RC lam),
      NIWI.accepts lam crsN (gateInst n m RC Com G lam i.val γ v)
        (fun j => (vright pf) (finProdFinEquiv (i, j)))

/-- **`R_NIZK((crs, x), π) = 1 ⟺ NIZK.V(crs, x, π) = 1` (§7.2, p. 61)**, with instance
`(crs, x)` and witness `π ∈ {0,1}^{ℓ_π}`. -/
def nizkRel : NPRel where
  instLen := fun lam => crsLen n m RC Com G NIWI lam + n lam
  witLen := proofLen n m RC Com G NIWI
  holds := fun lam X pf => verify n m RC Com G NIWI lam (vleft X) (vright X) pf

/-- **`Π.P(crs, x, w; r)` (Algorithm 1)**: evaluate `C_{n_x, n_w}(x, w)`; represent every public
wire by its padded bit and every private wire `a` by `Com(crs_Com, ω_a; r_a)`; for every gate `i`
prove `(X_i, v)` with `NIWI.P(crs_NIWI, (X_i, v), (0, τ_i))`; output `(γ_1, …, γ_k, π_1, …, π_g)`.
(At fixed lengths only `R(x, w) = 1` remains of the rejection checks; `WE'.Dec` performs it before
proving, so the prover circuit is the honest computation.) -/
def prove (lam : ℕ) :
    Circuit (crsLen n m RC Com G NIWI lam + n lam + m lam + proveTape n m RC Com G NIWI lam)
      (proofLen n m RC Com G NIWI lam) :=
  Circuit.build _ _ fun inp => do
    let crs := vleft (vleft (vleft inp))
    let x := vright (vleft (vleft inp))
    let w := vright (vleft inp)
    let coins := vright inp
    let crsCom : Fin (Com.crsLen lam) → ℕ := vleft (vleft crs)
    let crsN : Fin (NIWI.crsLen lam) → ℕ := vright (vleft crs)
    let v : Fin (2 * lam) → ℕ := vright crs
    let z ← BM.const false
    let one ← BM.const true
    let wv ← BM.embedAll (RC lam) (Fin.append x w)
    let K := numWires n m RC lam
    let ω : ℕ → ℕ := fun a => if a < K then wv a else z
    let opening : ℕ → Fin (Com.randLen lam) → ℕ := fun a j =>
      if h : a < K then
        (if isPublic n m RC lam a then z else (vleft coins) (finProdFinEquiv (⟨a, h⟩, j)))
      else z
    let γv ← BM.vec K fun a =>
      if isPublic n m RC lam a.val then
        pure (fun j : Fin (Com.comLen lam) => if j.val = 0 then ω a.val else z)
      else
        BM.embed (Com.com lam) (Fin.append (Fin.append crsCom (fun _ => ω a.val)) (opening a.val))
    let γ : ℕ → Fin (Com.comLen lam) → ℕ := fun a => if h : a < K then γv ⟨a, h⟩ else fun _ => z
    let lr := Com.randLen lam
    let πv ← BM.vec (numGates n m RC lam) fun i => do
      let gt := gateAt n m RC lam i.val
      let o := n lam + m lam + i.val
      let inst : Fin ((orGateRel n m RC Com G).instLen lam) → ℕ :=
        Fin.append (Fin.append (Fin.append (Fin.append
          (fun j : Fin (idxLen n m RC lam) => if i.val.testBit j.val then one else z)
          (γ gt.l)) (γ gt.r)) (γ o)) v
      let τ : ℕ → ℕ := fun j =>
        if j = 0 then ω gt.l else if j = 1 then ω gt.r else if j = 2 then ω o
        else if h : j - 3 < lr then opening gt.l ⟨j - 3, h⟩
        else if h : j - 3 - lr < lr then opening gt.r ⟨j - 3 - lr, h⟩
        else if h : j - 3 - lr - lr < lr then opening o ⟨j - 3 - lr - lr, h⟩
        else z
      let wit : Fin ((orGateRel n m RC Com G).witLen lam) → ℕ := fun idx =>
        if idx.val = 0 then z else τ (idx.val - 1)
      BM.embed (NIWI.prove lam) (Fin.append (Fin.append (Fin.append crsN inst) wit)
        (fun j => (vright coins) (finProdFinEquiv (i, j))))
    pure (Fin.append (fun idx => let p := finProdFinEquiv.symm idx; γv p.1 p.2)
      (fun idx => let p := finProdFinEquiv.symm idx; πv p.1 p.2))

end GateNIZK

end AnyWE.CEFCorrectness


