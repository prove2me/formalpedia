-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_CorrectnessProofs
-- name    : AnyWE_CEFCorrectness_CorrectnessProofs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:52:41.768385+00:00
-- url     : https://prove2.me/theorems/aef3af80-9fec-437a-b1d0-f1015bd1cbc8
-- title:
--   CEF proofs of correctness of witness encryption, and their circuit-sampler form (Definitions 7.2 and 7.3)
-- statement:
--   Let $\mathrm{WE}$ be a witness encryption scheme for the relation $R$ of circuits $C_\lambda$, at polynomial instance and witness lengths $n(\lambda),m(\lambda)$.
--
--   **Definition 7.2.** For an instance family $\{x_\lambda\}$, $x_\lambda\in\{0,1\}^{n(\lambda)}$, and a bit $b$, the **correctness assertion** at $\lambda$ is
--   $$R(x_\lambda,w)=1\ \Longrightarrow\ \mathrm{WE.Dec}\big(\mathrm{WE.Enc}(x_\lambda,b;r_1),w;r_2\big)=b,$$
--   represented by the gate equations of $R$ (with $x_\lambda$ hardwired), of $\mathrm{WE.Enc}$ (with $x_\lambda,b$ hardwired) and of $\mathrm{WE.Dec}$, together with the displayed implication, where $w\in\{0,1\}^{m(\lambda)}$ are proper variables and $r_1,r_2$ independent random variables. $\mathrm{WE}$ has **$(t,s,\ell)$-CEF proofs of correctness** if for every family $\{x_\lambda\}$ and every $b$ the assertion family admits a $(t,s,\ell)$-CEF proof, and **$\ell$-CEF proofs of correctness** if such polynomials $t,s$ exist.
--
--   **Definition 7.3.** Both samplers sample $\mathrm{ct}\leftarrow\mathrm{WE.Enc}(x_\lambda,b)$ and use $\mathrm{ct}$ as auxiliary string; the first outputs $C_{x,\mathrm{ct}}$, the second $D_{x,b}$:
--   $$C_{x,\mathrm{ct}}(w;r)=\begin{cases}\mathrm{WE.Dec}(\mathrm{ct},w;r)&R(x,w)=1\\ \bot&\text{otherwise,}\end{cases}\qquad D_{x,b}(w)=\begin{cases}b&R(x,w)=1\\ \bot&\text{otherwise,}\end{cases}$$
--   with $\mathrm{ct}$ hardwired in $C_{x,\mathrm{ct}}$, independent encryption and evaluation tapes, and the same encoding of $0,1,\bot$. $\mathrm{WE}$ has **$(t,s,\ell)$-CEF proofs of correctness in circuit-sampler form** if for every family and bit these samplers admit a $(t,t,s,\ell)$-CEF proof of indistinguishability; **$\ell$-CEF proofs** in this form if such polynomials $t,s$ exist.
--
--   CEF proofs of correctness are what the SNARG construction of the paper (via Jin–Lu–Peng) consumes; unlike EF proofs, they can exist for schemes whose correctness is only statistical.
--
--   **Formalization Note.** The values $0,1,\bot$ are encoded as $(1,0),(1,1),(0,0)$; "$=b$" in the assertion is $\mathit{valid}\wedge(\mathit{bit}\leftrightarrow b)$. Hardwired bits are the constants $\top,\bot$. The implication's premise is the output variable of $R$'s computation. The witness variables are $(\mathrm{proper},0,i)$, the tapes $(\mathrm{random},1,j)$ and $(\mathrm{random},2,j)$; computations $0,1,2$ name their gates and outputs.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 60, Definition 7.2; p. 61, Definition 7.3

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_Primitives
import Definitions.Def_AnyWE_CEFCorrectness_Sampler
set_option autoImplicit false

/-!
# CEF proofs of correctness of witness encryption (Definitions 7.2 and 7.3)

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), Definition 7.2 p. 60 and Definition 7.3 p. 61.

`W` is a witness encryption scheme for the relation `R` given by the circuits `RC`, at instance
length `n(λ)` and witness length `m(λ)`. Outputs in `{0, 1, ⊥}` are encoded by two bits
`(valid, bit)`, with `⊥ = (0, 0)` and `b = (1, b)`.
-/

namespace AnyWE.CEFCorrectness

namespace Correctness

variable {n m : ℕ → ℕ} (RC : ∀ lam, Circuit (n lam + m lam) 1) (W : WEScheme (relOf n m RC))

/-- **The correctness assertion of Definition 7.2** at `λ` for the hardwired instance `x = x_λ`
and bit `b`:
`R(x, w) = 1 ⟹ WE.Dec(WE.Enc(x, b; r₁), w; r₂) = b`, represented by the gate equations of `R`
(computation 0, on `x` hardwired and `w`), of `WE.Enc` (computation 1, on `x, b` hardwired and
`r₁`), of `WE.Dec` (computation 2, on the ciphertext, `x` hardwired, `w` and `r₂`), together with
the displayed implication. `w` are the proper variables `(proper, 0, i)`; `r₁`, `r₂` are the
random variables `(random, 1, j)`, `(random, 2, j)`. -/
def assertion (lam : ℕ) (x : Bits (n lam)) (b : Bool) : Finset Formula :=
  compEqs 0 (RC lam) (Fin.append (constIn x) (varsIn (m lam) .proper 0)) ∪
  compEqs 1 (W.enc lam)
    (Fin.append (Fin.append (constIn x) (fun _ => Formula.ofBool b))
      (varsIn (W.encTape lam) .random 1)) ∪
  compEqs 2 (W.dec lam)
    (Fin.append (Fin.append (Fin.append (fun j : Fin (W.ctLen lam) => compOut 1 j.val)
      (constIn x)) (varsIn (m lam) .proper 0)) (varsIn (W.decTape lam) .random 2)) ∪
  {Formula.imp (compOut 0 0) (Formula.and (compOut 2 0) (Formula.iff (compOut 2 1) (Formula.ofBool b)))}

/-- **Definition 7.2.** `W` has `(t, s, ℓ)`-CEF proofs of correctness for the lengths `n, m`:
for every instance family `{x_λ}` and every bit `b`, the assertion family admits a
`(t, s, ℓ)`-CEF proof (at most `k` premises per Logical Inference). -/
def HasCEFProofs (k : ℕ) (t s ℓ : ℕ → ℕ) : Prop :=
  ∀ (x : ∀ lam, Bits (n lam)) (b : Bool), CEFProof k t s ℓ (fun lam => assertion RC W lam (x lam) b)

/-- `W` has `ℓ`-CEF proofs of correctness (Definition 7.2): such polynomials `t, s` exist. -/
def HasLCEFProofs (k : ℕ) (ℓ : ℕ → ℕ) : Prop :=
  ∃ t s : Polynomial ℕ, HasCEFProofs RC W k (fun lam => t.eval lam) (fun lam => s.eval lam) ℓ

/-- The hardwired bits of `x` as constant wires. -/
def constWires {L : ℕ} (x : Bits L) : BM (Fin L → ℕ) := BM.vec L fun i => BM.const (x i)

/-- The common generator of both samplers of Definition 7.3: `ct ← WE.Enc(x_λ, b)` on the
encryption tape, output `(aux, key) = (ct, ct)`. -/
def encGen (lam : ℕ) (x : Bits (n lam)) (b : Bool) :
    Circuit (W.encTape lam) (W.ctLen lam + W.ctLen lam) :=
  Circuit.build _ _ fun r => do
    let xs ← constWires x
    let bb ← BM.const b
    let ct ← BM.embed (W.enc lam) (Fin.append (Fin.append xs (fun _ => bb)) r)
    pure (Fin.append ct ct)

/-- **The first sampler of Definition 7.3**: `ct ← WE.Enc(x_λ, b)`, output `(ct, C_{x,ct})` with
`C_{x,ct}(w; r) = WE.Dec(ct, w; r)` if `R(x, w) = 1` and `⊥` otherwise (`ct` hardwired). -/
def samplerC (lam : ℕ) (x : Bits (n lam)) (b : Bool) : SamplerAt (m lam) (W.ctLen lam) 2 where
  genLen := W.encTape lam
  keyLen := W.ctLen lam
  tapeLen := W.decTape lam
  gen := encGen RC W lam x b
  tmpl := Circuit.build _ _ fun inp => do
    let ct := vleft (vleft inp)
    let w := vright (vleft inp)
    let xs ← constWires x
    let ok ← BM.embed (RC lam) (Fin.append xs w)
    let d ← BM.embed (W.dec lam) (Fin.append (Fin.append (Fin.append ct xs) w) (vright inp))
    let valid ← BM.and (ok 0) (d 0)
    let bit ← BM.and valid (d 1)
    pure ![valid, bit]

/-- **The second sampler of Definition 7.3**: the same `ct ← WE.Enc(x_λ, b)`, output
`(ct, D_{x,b})` with `D_{x,b}(w) = b` if `R(x, w) = 1` and `⊥` otherwise. -/
def samplerD (lam : ℕ) (x : Bits (n lam)) (b : Bool) : SamplerAt (m lam) (W.ctLen lam) 2 where
  genLen := W.encTape lam
  keyLen := W.ctLen lam
  tapeLen := 0
  gen := encGen RC W lam x b
  tmpl := Circuit.build _ _ fun inp => do
    let w := vright (vleft inp)
    let xs ← constWires x
    let ok ← BM.embed (RC lam) (Fin.append xs w)
    let bit ← if b then pure (ok 0) else BM.const false
    pure ![ok 0, bit]

/-- **Definition 7.3.** `W` has `(t, s, ℓ)`-CEF proofs of correctness in circuit-sampler form:
for every instance family and bit the two samplers admit a `(t, t, s, ℓ)`-CEF proof of
indistinguishability. -/
def HasSamplerCEFProofs (k : ℕ) (t s ℓ : ℕ → ℕ) : Prop :=
  ∀ (x : ∀ lam, Bits (n lam)) (b : Bool),
    CEFIndist k t t s ℓ (fun lam => samplerC RC W lam (x lam) b) (fun lam => samplerD RC W lam (x lam) b)

/-- `W` has `ℓ`-CEF proofs of correctness in circuit-sampler form: such polynomials `t, s`
exist. -/
def HasLSamplerCEFProofs (k : ℕ) (ℓ : ℕ → ℕ) : Prop :=
  ∃ t s : Polynomial ℕ, HasSamplerCEFProofs RC W k (fun lam => t.eval lam) (fun lam => s.eval lam) ℓ

end Correctness

end AnyWE.CEFCorrectness


