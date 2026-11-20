-- Prove2me | Definitions.Def_GaoQuantumUnion_Decoding
-- name    : GaoQuantumUnion_Decoding
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-19T21:46:38.442343+00:00
-- url     : https://prove2.me/theorems/5406c89c-fd62-485f-82d7-f475f5ed41bd
-- title:
--   Sequential decoder effects and independently sampled finite codebooks
-- statement:
--   The rejection prefix at position $m$ is $(I-Q_{m-1})\cdots(I-Q_0)$, with empty prefix $I$. The accepting Kraus operator is $Q_m(I-Q_{m-1})\cdots(I-Q_0)P$, and its effect is $K_m^\dagger K_m$. A codebook is a function $C:\mathrm{Fin}(M)\to J$, including repeated codewords; its independent sampling weight is $\prod_m p(C_m)$. Its average decoding error uses the uniform average over the $M$ message positions and the trace of each accepting branch. The coding theorem explicitly requires $M>0$, avoiding the total-definition value at zero.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; PDF pp. 10–13: random codebook, sequential decoder, equations (25)–(26)

import Definitions.Def_GaoQuantumUnion_Model
import Definitions.Def_WildeQIT_Gentle_averageState
noncomputable section
open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
namespace GaoQuantumUnion
variable {ι J : Type} [Fintype ι] [DecidableEq ι]
def rejectPrefix {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) : Matrix ι ι ℂ :=
  ((List.ofFn (fun i => 1-Q i)).take m.val).foldl (fun K P => P*K) 1
def decoderK {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) : Matrix ι ι ℂ :=
  Q m*rejectPrefix Q m*P
def decoderEffect {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) : Matrix ι ι ℂ :=
  (decoderK P Q m)ᴴ*decoderK P Q m
def codeWeight [Fintype J] {M : ℕ} (p : FinDist J) (C : Fin M → J) : ℝ :=
  ∏ m, p.prob (C m)
def codeError {M : ℕ} (ρ : J → Matrix ι ι ℂ) (P : Matrix ι ι ℂ)
    (Q : J → Matrix ι ι ℂ) (C : Fin M → J) : ℝ :=
  1-(1/(M : ℝ))*∑ m, ((decoderK P (Q ∘ C) m)*ρ (C m)*(decoderK P (Q ∘ C) m)ᴴ).trace.re
end GaoQuantumUnion


