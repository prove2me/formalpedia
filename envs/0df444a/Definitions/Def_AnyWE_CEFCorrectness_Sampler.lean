-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_Sampler
-- name    : AnyWE_CEFCorrectness_Sampler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:51:49.663991+00:00
-- url     : https://prove2.me/theorems/9268b103-b156-4d48-8fd3-0b4b6847c68f
-- title:
--   Circuit samplers, PEF cryptographic gadget substitution, PEF and CEF proofs of indistinguishability (Definitions 5.1-5.4)
-- statement:
--   **Circuit samplers (Definition 5.1).** At a fixed $\lambda$, a sampler with input length $n$, auxiliary-string length $a$ and output length $o$ consists of a circuit $\mathrm{Gen}$ on a generation tape $\rho$ that outputs $(\mathrm{aux},k)$, and a fixed template circuit $T$; the sampled probabilistic circuit is $C_k(x;r)=T(k,x,r)$ (the template with the key $k$ hardwired). Its encoding length is that of $\mathrm{Gen}$ plus that of $T$. The **correctness assertion** for a deterministic circuit $F$ on $n$ bits is the set of gate equations of $\mathrm{Gen}$ on $\rho$, of $T$ on $(k,x,r)$ and of $F$ on $x$, together with the equalities of the two outputs; $x$ are proper variables, and $\rho,r$ are random variables (or proper variables, in an EF proof).
--
--   **Gadget substitution (Definition 5.2).** Samplers $\mathrm{Gen}_0,\mathrm{Gen}_1$ (same $n,a,o$) are related by a $(t,s,\ell,\epsilon)$-PEF cryptographic gadget substitution if there is a generator $\mathrm{Gen}'$, on the same generation tape, sampling $(\mathrm{aux}',K)$, and templates $C_{\mathrm{pre}}(K,x;r_{\mathrm{pre}})\to z$, $f^{(b)}(K,z;r_{\mathrm{mid}})\to y$, $C_{\mathrm{post}}(K,x,y;r_{\mathrm{post}})$ such that, with $D^{(b)}(x;r)=C_{\mathrm{post}}(x,f^{(b)}(C_{\mathrm{pre}}(x;r_{\mathrm{pre}});r_{\mathrm{mid}});r_{\mathrm{post}})$ and $r=(r_{\mathrm{pre}},r_{\mathrm{mid}},r_{\mathrm{post}})$:
--   - *EF Equivalence*: for each $b$ an EF proof, with $\rho,x,r$ proper variables, of $\mathrm{aux}^{(b)}=\mathrm{aux}'$ and $C^{(b)}_{k_b}(x;r)=D^{(b)}(x;r)$ (gate equations of all computations plus the equalities), of space at most $s$;
--   - *Indistinguishability*: for every circuit $D$ of size at most $1/\epsilon$ and every fixed $z$,
--   $$\Big|\Pr\big[D(\mathrm{aux}',K,y^{(0)})=1\big]-\Pr\big[D(\mathrm{aux}',K,y^{(1)})=1\big]\Big|\le\epsilon,\qquad y^{(b)}\leftarrow f^{(b)}(z;r_{\mathrm{mid}}),$$
--   with $(\mathrm{aux}',K)\leftarrow\mathrm{Gen}'$ and fresh gadget coins;
--   - *Gadget Size*: $|z|\le\log s$, or $|z|\le\ell$ and $|y|\le\log\ell$.
--
--   **PEF proofs of indistinguishability (Definition 5.3).** $\mathrm{Gen}^{(0)},\mathrm{Gen}^{(1)}$ admit an $(m,t,s,\ell,\epsilon)$-PEF proof of indistinguishability if there is a sequence $\mathrm{Gen}_0=\mathrm{Gen}^{(0)},\dots,\mathrm{Gen}_{m'}=\mathrm{Gen}^{(1)}$, $m'\le m$, each step being a gadget substitution (with its witnesses) or an *indistinguishability of sampler outputs* step (both samplers have the same template, and every $D$ of size at most $1/\epsilon$ distinguishes their outputs $(\mathrm{aux},k)$ with advantage at most $\epsilon$), such that the samplers, decompositions and EF proofs have total encoding length at most $t$, and every EF proof has space at most $s$.
--
--   **CEF proofs of indistinguishability (Definition 5.4).** For functions $m,t,s,\ell$ of $\lambda$, one family of sampler sequences with rules and witnesses, fixed independently of $c$, which for every $c>0$ and all sufficiently large $\lambda$ is an $(m(\lambda),t(\lambda),s(\lambda),\ell(\lambda),\lambda^{-c})$-PEF proof of indistinguishability.
--
--   These notions express that two ways of sampling a circuit are related by a short chain of locally justified cryptographic or logical steps; Theorem 5.6 turns such a chain into a CEF proof of correctness.
--
--   **Formalization Note.** Following the paper's convention before Theorem 5.6 (hardwired data in a fixed template is identified with universal-circuit evaluation), a sampled circuit is a template plus key; its description given to distinguishers is the key (the template is fixed), so an output step requires the same template, and a change of template goes through EF equivalences. EF Equivalence is one EF proof per $b$ of both equalities; the EF proofs' lengths are counted in the encoding length.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), pp. 39-41, Definitions 5.1-5.4, and p. 41 (convention before Theorem 5.6)

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_PEF
set_option autoImplicit false

/-!
# Circuit samplers, PEF gadget substitution, PEF and CEF proofs of indistinguishability

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), Definitions 5.1–5.4, pp. 39–41, and the convention before
Theorem 5.6, p. 41 ("For circuits obtained by hardwiring data into a fixed circuit template, we
freely identify universal-circuit evaluation with the direct computation").

A sampler at a fixed `λ` is a circuit `gen` on its generation tape `ρ` that outputs
`(aux, k)`, together with a fixed circuit template `tmpl`; the sampled probabilistic circuit is
`C_k(x; r) = tmpl(k, x, r)`, the template with the key `k` hardwired. Its description, given to
distinguishers, is the key `k` (the template is fixed); a step between samplers with different
templates goes through EF equivalences (a gadget substitution).
-/

namespace AnyWE.CEFCorrectness

/-- A circuit sampler at a fixed `λ` with input length `n`, auxiliary-string length `a` and output
length `o` (Definition 5.1). -/
structure SamplerAt (n a o : ℕ) where
  genLen : ℕ
  keyLen : ℕ
  tapeLen : ℕ
  gen : Circuit genLen (a + keyLen)
  tmpl : Circuit (keyLen + n + tapeLen) o

namespace SamplerAt

variable {n a o : ℕ}

/-- The encoding length of a sampler: its generator and its template. -/
def encLen (S : SamplerAt n a o) : ℕ := S.gen.encLen + S.tmpl.encLen

/-- Two samplers have the same template (same key and tape lengths, same circuit). -/
def SameTemplate (S S' : SamplerAt n a o) : Prop :=
  S.keyLen = S'.keyLen ∧ S.tapeLen = S'.tapeLen ∧ S.tmpl.gates = S'.tmpl.gates ∧
    ∀ i, S.tmpl.out i = S'.tmpl.out i

/-- The assertion `C_k(x; r) = F(x), (aux, C_k) ← Gen(1^λ; ρ)` as a set of formulas (Theorem 5.6):
the gate equations of `Gen` on `ρ` (computation 0), of the sampled circuit on `(k, x, r)`
(computation 1) and of `F` on `x` (computation 2), and the equalities of the two outputs.
`x` are the proper variables `(proper, 0, i)`; `ρ` and `r` are the variables `(κ, 1, j)` and
`(κ, 2, j)`: random variables (`κ = random`) in the PEF assertion, proper variables
(`κ = proper`) in an EF proof. -/
def corrAssertion (S : SamplerAt n a o) (F : Circuit n o) (κ : VarKind) : Finset Formula :=
  compEqs 0 S.gen (varsIn S.genLen κ 1) ∪
  compEqs 1 S.tmpl (Fin.append (Fin.append (fun j : Fin S.keyLen => compOut 0 (a + j.val))
      (varsIn n .proper 0)) (varsIn S.tapeLen κ 2)) ∪
  compEqs 2 F (varsIn n .proper 0) ∪
  Finset.univ.image (fun i : Fin o => Formula.iff (compOut 1 i.val) (compOut 2 i.val))

end SamplerAt

/-- The data of a PEF cryptographic gadget substitution (Definition 5.2): a generator `Gen'`
sampling `(aux', K)` on the generation tape, and the templates of `C_pre`, `f^(0)`, `f^(1)`,
`C_post`, all with the hardwired data `K`; and the supplied EF proofs, one for each `b`. -/
structure GadgetData (n a o : ℕ) where
  genLen : ℕ
  keyLen : ℕ
  preTape : ℕ
  zLen : ℕ
  yLen : ℕ
  mid0 : ℕ
  mid1 : ℕ
  postTape : ℕ
  gen : Circuit genLen (a + keyLen)
  pre : Circuit (keyLen + n + preTape) zLen
  f0 : Circuit (keyLen + zLen + mid0) yLen
  f1 : Circuit (keyLen + zLen + mid1) yLen
  post : Circuit (keyLen + n + yLen + postTape) o
  ef0 : List (Finset Formula)
  ef1 : List (Finset Formula)

namespace GadgetData

variable {n a o : ℕ}

/-- The encoding length of the decomposition and of the supplied EF proofs. -/
def encLen (G : GadgetData n a o) : ℕ :=
  G.gen.encLen + G.pre.encLen + G.f0.encLen + G.f1.encLen + G.post.encLen +
    derivLength G.ef0 + derivLength G.ef1

/-- The EF Equivalence assertion for `b` (Definition 5.2): with `ρ, x, r` proper variables and
`r = (r_pre, r_mid, r_post)`, the gate equations of `Gen_b` on `ρ` (computation 0), of
`C^(b)_{k_b}(x; r)` (1), of `Gen'` on `ρ` (2), of `z := C_pre(x; r_pre)` (3),
`y := f^(b)(z; r_mid)` (4), `u := C_post(x, y; r_post)` (5), and the equalities
`aux^(b) = aux'` and `C^(b)_{k_b}(x; r) = D^(b)(x; r)`. -/
def equivAssertion (G : GadgetData n a o) (S : SamplerAt n a o) (b : Bool) : Finset Formula :=
  let mid := if b then G.mid1 else G.mid0
  let K : Fin G.keyLen → Formula := fun j => compOut 2 (a + j.val)
  let x := varsIn n .proper 0
  compEqs 0 S.gen (varsIn S.genLen .proper 1) ∪
  compEqs 1 S.tmpl (Fin.append (Fin.append (fun j : Fin S.keyLen => compOut 0 (a + j.val)) x)
      (varsIn S.tapeLen .proper 2)) ∪
  compEqs 2 G.gen (varsIn G.genLen .proper 1) ∪
  compEqs 3 G.pre (Fin.append (Fin.append K x) (varsIn G.preTape .proper 2)) ∪
  (if b then
      compEqs 4 G.f1 (Fin.append (Fin.append K (fun j : Fin G.zLen => compOut 3 j.val))
        (varsIn G.mid1 .proper 2 G.preTape))
    else
      compEqs 4 G.f0 (Fin.append (Fin.append K (fun j : Fin G.zLen => compOut 3 j.val))
        (varsIn G.mid0 .proper 2 G.preTape))) ∪
  compEqs 5 G.post (Fin.append (Fin.append (Fin.append K x)
      (fun j : Fin G.yLen => compOut 4 j.val)) (varsIn G.postTape .proper 2 (G.preTape + mid))) ∪
  Finset.univ.image (fun i : Fin a => Formula.iff (compOut 0 i.val) (compOut 2 i.val)) ∪
  Finset.univ.image (fun i : Fin o => Formula.iff (compOut 1 i.val) (compOut 5 i.val))

/-- `(aux', K) ← Gen'(1^λ; ρ)`. -/
def sample (G : GadgetData n a o) (ρ : Bits G.genLen) : Bits (a + G.keyLen) := G.gen.eval ρ

/-- `y^(0) ← f^(0)(z; r_mid)` with the key of `Gen'`'s output `K`. -/
def eval0 (G : GadgetData n a o) (aK : Bits (a + G.keyLen)) (z : Bits G.zLen)
    (r : Bits G.mid0) : Bits G.yLen :=
  G.f0.eval (Fin.append (Fin.append aK.right z) r)

/-- `y^(1) ← f^(1)(z; r_mid)`. -/
def eval1 (G : GadgetData n a o) (aK : Bits (a + G.keyLen)) (z : Bits G.zLen)
    (r : Bits G.mid1) : Bits G.yLen :=
  G.f1.eval (Fin.append (Fin.append aK.right z) r)

/-- **(t, s, ℓ, ϵ)-PEF cryptographic gadget substitution between `S₀` and `S₁` (Definition 5.2)**,
with at most `k` premises per Logical Inference in the EF proofs: the same generation tape for
`S₀, S₁, Gen'`; tapes `r = (r_pre, r_mid^(b), r_post)`; EF Equivalence (for each `b`, an EF proof of
`equivAssertion G S_b b` of space at most `s`; their lengths are counted in the encoding length);
Indistinguishability (every `D` of size at most `1/ϵ` and every fixed gadget input `z`: advantage at
most `ϵ` on `(aux', K, y^(b))`, with `(aux', K)` and the gadget coins sampled); and Gadget Size. -/
def Valid (G : GadgetData n a o) (k s ℓ : ℕ) (ϵ : ℝ) (S₀ S₁ : SamplerAt n a o) : Prop :=
  S₀.genLen = G.genLen ∧ S₁.genLen = G.genLen ∧
  S₀.tapeLen = G.preTape + G.mid0 + G.postTape ∧ S₁.tapeLen = G.preTape + G.mid1 + G.postTape ∧
  IsEFProof k (G.equivAssertion S₀ false) G.ef0 ∧ derivSpace G.ef0 ≤ s ∧
  IsEFProof k (G.equivAssertion S₁ true) G.ef1 ∧ derivSpace G.ef1 ≤ s ∧
  (∀ D : Circuit (a + G.keyLen + G.yLen) 1, (D.size : ℝ) ≤ 1 / ϵ → ∀ z : Bits G.zLen,
    |prob (G.genLen + G.mid0) (fun v =>
        D.eval (Fin.append (G.sample v.left) (G.eval0 (G.sample v.left) z v.right)) 0 = true) -
      prob (G.genLen + G.mid1) (fun v =>
        D.eval (Fin.append (G.sample v.left) (G.eval1 (G.sample v.left) z v.right)) 0 = true)|
      ≤ ϵ) ∧
  (2 ^ G.zLen ≤ s ∨ (G.zLen ≤ ℓ ∧ 2 ^ G.yLen ≤ ℓ))

end GadgetData

/-- The rule of one step of a proof of indistinguishability: a gadget substitution with its
witnesses, or indistinguishability of sampler outputs. -/
inductive IndistStep (n a o : ℕ)
  | gadget (G : GadgetData n a o)
  | output

/-- **Indistinguishability of sampler outputs (Definition 5.3)**: same template, and every `D` of
size at most `1/ϵ` given `(aux, k)` has advantage at most `ϵ`. -/
def OutputIndist {n a o : ℕ} (ϵ : ℝ) (S₀ S₁ : SamplerAt n a o) : Prop :=
  S₀.SameTemplate S₁ ∧
  ∀ D : Circuit (a + S₀.keyLen) 1, (D.size : ℝ) ≤ 1 / ϵ →
    |prob S₀.genLen (fun ρ => D.eval (S₀.gen.eval ρ) 0 = true) -
      prob S₁.genLen (fun ρ => D.eval ((S₁.gen.eval ρ).resize (a + S₀.keyLen)) 0 = true)| ≤ ϵ

/-- One step `S₀ → S₁` with its rule and witnesses. -/
def IndistStep.Valid {n a o : ℕ} (k s ℓ : ℕ) (ϵ : ℝ) (S₀ S₁ : SamplerAt n a o) :
    IndistStep n a o → Prop
  | .gadget G => G.Valid k s ℓ ϵ S₀ S₁
  | .output => OutputIndist ϵ S₀ S₁

/-- A sampler sequence `Gen_0, …, Gen_{m'}` with a rule and witnesses for each step. -/
structure IndistProof (n a o : ℕ) where
  samplers : List (SamplerAt n a o)
  steps : List (IndistStep n a o)

/-- The encoding length of a step's witnesses. -/
def IndistStep.encLen {n a o : ℕ} : IndistStep n a o → ℕ
  | .gadget G => G.encLen
  | .output => 0

/-- **(m, t, s, ℓ, ϵ)-PEF proof of indistinguishability from `S₀` to `S₁` at a fixed `λ`
(Definition 5.3)**: `Gen_0 = S₀`, `Gen_{m'} = S₁`, `m' ≤ m`, every step valid, total encoding
length of the samplers, decompositions and EF proofs at most `t`, every EF proof of space at
most `s`. -/
def IndistProof.Valid {n a o : ℕ} (P : IndistProof n a o) (k m t s ℓ : ℕ) (ϵ : ℝ)
    (S₀ S₁ : SamplerAt n a o) : Prop :=
  P.samplers.length = P.steps.length + 1 ∧ P.samplers.head? = some S₀ ∧
    P.samplers.getLast? = some S₁ ∧ P.steps.length ≤ m ∧
    (∀ (i : ℕ) (A B : SamplerAt n a o) (st : IndistStep n a o), P.samplers[i]? = some A →
      P.samplers[i + 1]? = some B → P.steps[i]? = some st → st.Valid k s ℓ ϵ A B) ∧
    (P.samplers.map SamplerAt.encLen).sum + (P.steps.map IndistStep.encLen).sum ≤ t

/-- `S₀, S₁` admit an `(m, t, s, ℓ, ϵ)`-PEF proof of indistinguishability (Definition 5.3). -/
def PEFIndistAt {n a o : ℕ} (k m t s ℓ : ℕ) (ϵ : ℝ) (S₀ S₁ : SamplerAt n a o) : Prop :=
  ∃ P : IndistProof n a o, P.Valid k m t s ℓ ϵ S₀ S₁

/-- **(m, t, s, ℓ)-CEF proof of indistinguishability (Definition 5.4)** of two sampler families:
one family of sampler sequences with rules and witnesses, fixed before `c`, which for every
constant `c > 0` and all sufficiently large `λ` is an `(m(λ), t(λ), s(λ), ℓ(λ), λ^{-c})`-PEF proof
of indistinguishability. -/
def CEFIndist (k : ℕ) (m t s ℓ : ℕ → ℕ) {n a o : ℕ → ℕ}
    (S₀ S₁ : ∀ lam, SamplerAt (n lam) (a lam) (o lam)) : Prop :=
  ∃ P : ∀ lam, IndistProof (n lam) (a lam) (o lam), ∀ c : ℝ, 0 < c → ∀ᶠ lam in Filter.atTop,
    (P lam).Valid k (m lam) (t lam) (s lam) (ℓ lam) ((lam : ℝ) ^ (-c)) (S₀ lam) (S₁ lam)

end AnyWE.CEFCorrectness


