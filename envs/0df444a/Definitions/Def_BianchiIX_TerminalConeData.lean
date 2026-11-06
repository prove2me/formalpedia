-- Prove2me | Definitions.Def_BianchiIX_TerminalConeData
-- name    : BianchiIX_TerminalConeData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T18:59:12.312252+00:00
-- url     : https://prove2.me/theorems/a3ae7cd2-a346-4fc1-bca2-781f8da888ac
-- title:
--   Terminal variations, reciprocal phases and natural cone maps
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   On the invariant plane with zero active wall, use $y=(m,u,w)\in\mathbb R^3$,
--   the inclusion $\iota(m,u,w)=(m,u,0,w)$ and the restriction
--   $\pi_s(m,u,v,w)=(m,u,w)$. Define
--   $$f(y)=\left(mu^2-(m+1)uw+w^2,
--   \frac{1-m^2-w^2+u^2}{2}u,-(m+1+uw-u^2)w\right),$$
--   $$\Delta(y)=3+m^2+(u-w)^2,\qquad f_o(y)=6f(y)/\Delta(y).$$
--   Write $J=df$, $H=d^2f$, $J_o=df_o$, $H_o=d^2f_o$ for their explicit
--   Jacobian and Hessian expressions. The denominator derivatives are
--   $d\Delta=(2m,2(u-w),2(w-u))$ and
--   $d^2\Delta(v,z)=2v_0z_0+2(v_1-v_2)(z_1-z_2)$.
--   The exact original-time boundary flow and its projected variation are
--   $$\Phi(y,t)=\pi_s\Psi_0(\iota y,t),\qquad
--   L(y,t)=\pi_s\mathcal J_{\iota y,0}(t)\iota.$$
--   For a fixed scale $K$, set $\Phi_K(y,s)=\Phi(y,Ks)$,
--   $L_K(y,s)=L(y,Ks)$ and $Q_K(y,s)=d_yL_K(y,s)$.
--   For directions $v,z$, define
--   $$S_K(y,s;v,z)=K\left[H_o(\Phi_K)(L_Kv,L_Kz)+J_o(\Phi_K)Q_K(v,z)\right].$$
--   All vector norms are sup norms, and operator norms are induced by them.
--   Write $b(y)=|u|+|w|$, $E(y)=e^{512b(y)}$, $v_s=(v_1,v_2)$, and
--   $$\mathcal H(y;v,z)=b(y)\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|,$$
--   $$B_2(y)=192b(y)(40000E(y)^3)+10000E(y)^2.$$
--   The closed boundary region is
--   $\mathcal S_c=\{(m,u,0,w):|m-c|\leq1/10,\ |u|,|w|\leq1/100\}$.
--   The boundary projection $P(m,u,w)$ is the limit of $\Phi(m,u,w;t)_0$
--   as $t\to\infty$, using the total limit convention of the formal definitions.
--
--   Set $p(y)=P(y_0,y_1,y_3)$, $\rho(y)=\sqrt{(p(y)-1)^2+y_2^2}$,
--   and $\chi(y)=(\rho(y),y_1,y_2,y_3)$.
--   An admissible inverse $\psi$ at $y$ is $C^2$ at $\chi(y)$,
--   maps $\chi(y)$ to $y$, and is a two-sided local inverse of $\chi$;
--   its derivative is the inverse of the triangular derivative of $\chi$.
--   In the following notation put $y_h=\mathcal A\circ P_h$ and
--   $z_h=\chi\circ y_h$. Define
--   $$F_h(Y)=r(\mathcal P(h,Y)_0,\mathcal P(h,Y)_2),\quad
--   D_h=F_h-(z_h)_0,\quad Q_h=2/F_h-2/(z_h)_0.$$
--   For $I(m,u)=(1+m^2+u^2)/m$ let
--   $$\lambda_+(I)=(I+\sqrt{I^2-4})/2,\qquad
--   s(m,u)=2/(\lambda_+(I(m,u))-1).$$
--   Set $S_h=s((y_h)_0,(y_h)_1)$,
--   $Q_h^s=2/(z_h)_0-S_h$, $E_h=2/F_h-S_h$, and $B_h=2/F_h$.
--   The positive wall multipliers $m_0,m_1$ are defined by integrating the
--   two multiplicative wall rates along the exact exit flow, so that
--   $(P_h)_1=u m_0$ and $(P_h)_3=w m_1$. Write
--   $B_i^h=4m_i/H(P_h)$ for $i=0,1$.
--   For $Y=(2+2\alpha,u,w)$ let $h=\eta\alpha^J$.
--   All derivatives of maps with subscript $h$ hold this height fixed.
--   A cone direction is $d=(1,d_1,d_2)$ with
--   $|d_1|\leq\sqrt u$, $|d_2|\leq\sqrt w$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   Let $\beta(Y,t)=\Psi_0(e_-(Y),t)$ and $c(Y,t)=-\log\beta(Y,t)_2$.
--   Call $(Y,t)$ regular when $Y_0>1$, $D(e_-(Y))>0$, the normalized
--   flow exists at $t$ with positive chart clock, and
--   $\beta_2>0$, $\beta_0<1$, $\omega(\beta)>0$.
--   For an interval $I$, let $\tau_I(Y,s)$ be a solution in $I$ of
--   $c(Y,t)=s$, selected by choice, or zero if there is none. Define
--   $$X_I(Y,s)=Q(\beta(Y,\tau_I(Y,s))),\qquad
--   \ell_i(Y,s)=\int_0^s a_i(X_I(Y,r)_0,X_I(Y,r)_1,e^{-r},X_I(Y,r)_2)\,dr.$$
--   Here $i=0,1$ denotes $a_s,a_w$ respectively. Write
--   $$V(\alpha,b,A,D,T)=2B(\alpha,b,A,D,T)+2048(1+AbT).$$
--   The tail box is $7/4\leq R\leq17/4$, $|u|,|w|\leq1/100$, $0\leq v\leq1$.
--   Write $G_R=\nabla_{R,u,w}f_R$, $G_s=\nabla_{R,u,w}a_s$,
--   $G_w=\nabla_{R,u,w}a_w$ for their explicit algebraic gradients there.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   On the invariant plane with zero active wall, use $y=(m,u,w)\in\mathbb R^3$,
--   the inclusion $\iota(m,u,w)=(m,u,0,w)$ and the restriction
--   $\pi_s(m,u,v,w)=(m,u,w)$. Define
--   $$f(y)=\left(mu^2-(m+1)uw+w^2,
--   \frac{1-m^2-w^2+u^2}{2}u,-(m+1+uw-u^2)w\right),$$
--   $$\Delta(y)=3+m^2+(u-w)^2,\qquad f_o(y)=6f(y)/\Delta(y).$$
--   Write $J=df$, $H=d^2f$, $J_o=df_o$, $H_o=d^2f_o$ for their explicit
--   Jacobian and Hessian expressions. The denominator derivatives are
--   $d\Delta=(2m,2(u-w),2(w-u))$ and
--   $d^2\Delta(v,z)=2v_0z_0+2(v_1-v_2)(z_1-z_2)$.
--   The exact original-time boundary flow and its projected variation are
--   $$\Phi(y,t)=\pi_s\Psi_0(\iota y,t),\qquad
--   L(y,t)=\pi_s\mathcal J_{\iota y,0}(t)\iota.$$
--   For a fixed scale $K$, set $\Phi_K(y,s)=\Phi(y,Ks)$,
--   $L_K(y,s)=L(y,Ks)$ and $Q_K(y,s)=d_yL_K(y,s)$.
--   For directions $v,z$, define
--   $$S_K(y,s;v,z)=K\left[H_o(\Phi_K)(L_Kv,L_Kz)+J_o(\Phi_K)Q_K(v,z)\right].$$
--   All vector norms are sup norms, and operator norms are induced by them.
--   Write $b(y)=|u|+|w|$, $E(y)=e^{512b(y)}$, $v_s=(v_1,v_2)$, and
--   $$\mathcal H(y;v,z)=b(y)\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|,$$
--   $$B_2(y)=192b(y)(40000E(y)^3)+10000E(y)^2.$$
--   The closed boundary region is
--   $\mathcal S_c=\{(m,u,0,w):|m-c|\leq1/10,\ |u|,|w|\leq1/100\}$.
--   The boundary projection $P(m,u,w)$ is the limit of $\Phi(m,u,w;t)_0$
--   as $t\to\infty$, using the total limit convention of the formal definitions.
--
--   Write $\pi_s(m,u,v,w)=(m,u,w)$,
--   $R_s(m,u,w)=P(m,u,w)-P(m,u,0)$,
--   $p(y)=P(\pi_s y)$, $\rho_s(y)=P(y_0,y_1,0)-1$,
--   $\rho(y)=\sqrt{(p(y)-1)^2+y_2^2}$ and
--   $\chi(y)=(\rho(y),y_1,y_2,y_3)$.
--   Put $E_s=\rho-\rho_s$ and $Q_s=2/\rho-2/\rho_s$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
--
--   Define
--   $$H_0=(2-g(R,v))^2+v^2,\quad d_0=(u-w)^2-2v(u+w),$$
--   $$e=d_0[1+(R^2-4+d_0)/H_0],\qquad
--   \sigma_v(R,u,w)=(\sqrt{R^2+e}-2)/2.$$
--   Put
--   $$H_{0,R}=2(g-2)R/g,\quad
--   e_R=d_0[2R/H_0-(R^2-4+d_0)H_{0,R}/H_0^2],$$
--   $$e_{\rm wall}=1+(R^2-4+2d_0)/H_0.$$
--
--   The exit linearization is
--   $\xi\mapsto(G_R\cdot\xi,uG_s\cdot\xi+a_s\xi_1,
--   wG_w\cdot\xi+a_w\xi_2)$; its time-dependent second-variation source
--   is obtained by differentiating this expression along the exit clock flow.
--   The physical-time exit clock rate is $6\omega/D$.
--   For the cyclic map write $N=(-4(m+1),4v,4w,4u)$, so
--   $\mathcal A=(1,0,0,0)+N/H$; its derivative and Hessian are the
--   quotient-rule expressions using $N'$, $dH$, and $d^2H$.
--   The natural height is $h_*(Y)=\eta((Y_0-2)/2)^J$.
--   The natural state and phase are $\mathcal P(h_*(Y),Y)$ and
--   $F_{h_*(Y)}(Y)$. These definitions also include
--   $\lambda_-(I)=(I-\sqrt{I^2-4})/2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_BianchiIX_TerminalConnectionData
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def intervalScalarInverse {E : Type*} (Q : E × ℝ → ℝ) (I : Set ℝ) (p : E × ℝ) : ℝ := by
  classical
  exact if h : ∃ t ∈ I, Q (p.1, t) = p.2 then Classical.choose h else 0









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def singleStrongInvariant (m u : ℝ) : ℝ := (1 + m ^ 2 + u ^ 2) / m

def singleStrongUpperRoot (I : ℝ) : ℝ := (I + Real.sqrt (I ^ 2 - 4)) / 2

def singleStrongLowerRoot (I : ℝ) : ℝ := (I - Real.sqrt (I ^ 2 - 4)) / 2

def singleStrongPhase (m u : ℝ) : ℝ := 2 / (singleStrongUpperRoot (singleStrongInvariant m u) - 1)





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitSingleBase (R v : ℝ) : ℝ := (2 - exitTailGap R v) ^ 2 + v ^ 2

def exitSingleDefect (u v w : ℝ) : ℝ := (u - w) ^ 2 - 2 * v * (u + w)

def exitSingleError (R u v w : ℝ) : ℝ :=
  exitSingleDefect u v w * (1 + (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v)

def exitSinglePhase (R u v w : ℝ) : ℝ := (Real.sqrt (R ^ 2 + exitSingleError R u v w) - 2) / 2















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitTailRadialGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let g := exitTailRadial R u v w
  ![(-coupling u v w - (1 / t - t / R ^ 2) * (u - w) ^ 2 - g * R / t) / d,
    (-(v + w - 2 * u) * R - 2 * t * (u - w) / R - g * (v + w - 2 * u)) / d,
    (-u * R + 2 * t * (u - w) / R - g * u) / d]

def exitTailStrongRateGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let a := exitTailStrongRate R u v w
  ![(R / t - R - a * R / t) / d,
    (u - a * (v + w - 2 * u)) / d, (v - w - a * u) / d]

def exitTailWeakRateGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let a := exitTailWeakRate R u v w
  ![((1 - a) * R / t) / d,
    (-(1 + a) * (v + w - 2 * u)) / d, (-(1 + a) * u) / d]









def exitTailLinearization (v : ℝ) (Y ξ : ExitTailState) : ExitTailState :=
  ![∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i,
    Y 1 * (∑ i : Fin 3, exitTailStrongRateGradient (Y 0) (Y 1) v (Y 2) i * ξ i) +
      exitTailStrongRate (Y 0) (Y 1) v (Y 2) * ξ 1,
    Y 2 * (∑ i : Fin 3, exitTailWeakRateGradient (Y 0) (Y 1) v (Y 2) i * ξ i) +
      exitTailWeakRate (Y 0) (Y 1) v (Y 2) * ξ 2]





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitLogClock (y : ProjectiveState) : ℝ := -Real.log (y 2)

def exitOriginalClockRate (y : ProjectiveState) : ℝ :=
  (6 / projectiveStateDenom y) * exitClockRate y















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitSingleBaseRadial (R v : ℝ) : ℝ := 2 * (exitTailGap R v - 2) * R / exitTailGap R v

def exitSingleErrorRadial (R u v w : ℝ) : ℝ :=
  exitSingleDefect u v w * (2 * R / exitSingleBase R v -
    (R ^ 2 - 4 + exitSingleDefect u v w) * exitSingleBaseRadial R v / (exitSingleBase R v) ^ 2)

def exitSingleErrorWallFactor (R u v w : ℝ) : ℝ :=
  1 + (R ^ 2 - 4 + 2 * exitSingleDefect u v w) / exitSingleBase R v



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open scoped Topology

def cycleNumerator (i : Fin 4) (y : ProjectiveState) : ℝ :=
  ![-4 * (y 0 + 1), 4 * y 2, 4 * y 3, 4 * y 1] i

def cycleNumeratorSlope (i : Fin 4) (v : ProjectiveState) : ℝ :=
  ![-4 * v 0, 4 * v 2, 4 * v 3, 4 * v 1] i

def cycleDenomDifferential (y v : ProjectiveState) : ℝ :=
  2 * (y 0 + 1) * v 0 + 2 * (y 1 - y 2 - y 3) * v 1 +
    2 * (y 2 - y 1 - y 3) * v 2 + 2 * (y 3 - y 1 - y 2) * v 3

def cycleDenomHessian (v w : ProjectiveState) : ℝ :=
  2 * (v 0 * w 0 + (v 1 - v 2 - v 3) * w 1 +
    (v 2 - v 1 - v 3) * w 2 + (v 3 - v 1 - v 2) * w 3)

def cycleDifferential (i : Fin 4) (y v : ProjectiveState) : ℝ :=
  cycleNumeratorSlope i v / projectiveCycleDenom y -
    cycleNumerator i y * cycleDenomDifferential y v / projectiveCycleDenom y ^ 2

def cycleHessian (i : Fin 4) (y v w : ProjectiveState) : ℝ :=
  -(cycleNumeratorSlope i v * cycleDenomDifferential y w +
    cycleNumeratorSlope i w * cycleDenomDifferential y v +
    cycleNumerator i y * cycleDenomHessian v w) / projectiveCycleDenom y ^ 2 +
    2 * cycleNumerator i y * cycleDenomDifferential y v * cycleDenomDifferential y w /
      projectiveCycleDenom y ^ 3



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitTailRateGradient (v : ℝ) (Y : ExitTailState) (i : Fin 2) : ExitTailState :=
  if i = 0 then exitTailStrongRateGradient (Y 0) (Y 1) v (Y 2)
  else exitTailWeakRateGradient (Y 0) (Y 1) v (Y 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailVariationBudget (α b A D T : ℝ) : ℝ :=
  2 * exitTailRateBudget α b A D T + 2048 * (1 + A * b * T)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitEntryFlow (p : ExitTailState × ℝ) : ProjectiveState :=
  projectiveOriginalFlow (coreTailEntry p.1) 0 p.2

def exitEntryClock (p : ExitTailState × ℝ) : ℝ := exitLogClock (exitEntryFlow p)

def exitEntryRegular (Y : ExitTailState) (t : ℝ) : Prop :=
  1 < Y 0 ∧ 0 < projectiveStateDenom (coreTailEntry Y) ∧
    t ∈ normalizedMaxDomain (fromProjectiveState (coreTailEntry Y)) 0 ∧
    0 < 1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry Y)) 0 t 0 ∧
    0 < exitEntryFlow (Y, t) 2 ∧ exitEntryFlow (Y, t) 0 < 1 ∧
    0 < exitClockRate (exitEntryFlow (Y, t))















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitClockTime (I : Set ℝ) : ExitTailState × ℝ → ℝ := intervalScalarInverse exitEntryClock I

def exitClockFlow (I : Set ℝ) (p : ExitTailState × ℝ) : ExitTailState :=
  toExitTailState (exitEntryFlow (p.1, exitClockTime I p))



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitClockVariationRate (I : Set ℝ) (w : ExitTailState) (p : ExitTailState × ℝ) : ExitTailState :=
  fderiv ℝ (exitTailField (Real.exp (-p.2))) (exitClockFlow I p)
    (fderiv ℝ (exitClockFlow I) p (w, 0))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def exitClockRateIntegrand (I : Set ℝ) (i : Fin 2) (p : ExitTailState × ℝ) : ℝ :=
  exitTailWallRate (Real.exp (-p.2)) (exitClockFlow I p) i

def exitClockLogMultiplier (I : Set ℝ) (i : Fin 2) (Y : ExitTailState) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, exitClockRateIntegrand I i (Y, r)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def terminalCyclicInput (h : ℝ) (Y : ExitTailState) : ProjectiveState :=
  projectiveCycle (coreTailState h Y)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalSinglePhase (h : ℝ) (Y : ExitTailState) : ℝ :=
  singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def terminalEntranceInput (h : ℝ) (Y : ExitTailState) : ProjectiveState :=
  entranceRadialCoordinates (terminalCyclicInput h Y)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Indices 0 and 1 transport the old U and W walls to the new w and v walls, respectively. -/
def terminalWallFactor (h : ℝ) (Y : ExitTailState) (i : Fin 2) : ℝ :=
  4 * coreTailMultiplier h Y i / projectiveCycleDenom (coreTailState h Y)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalConnectionPhase (h : ℝ) (Y : ExitTailState) : ℝ :=
  coreRadius (terminalConnectionState h Y 0) (terminalConnectionState h Y 2)

def terminalConnectionError (h : ℝ) (Y : ExitTailState) : ℝ :=
  terminalConnectionPhase h Y - terminalEntranceInput h Y 0







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def terminalReciprocalError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalConnectionPhase h Y - 2 / terminalEntranceInput h Y 0



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableStrongBase : StableState →L[ℝ] StableState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]





def stableStrongProjectionError (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableBoundaryProjection (y 0) (y 1) 0











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceSinglePhaseError (y : ProjectiveState) : ℝ :=
  entranceStableRadius y - (stableBoundaryProjection (y 0) (y 1) 0 - 1)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceSingleRadius (y : ProjectiveState) : ℝ := stableBoundaryProjection (y 0) (y 1) 0 - 1

def entranceSingleReciprocalError (y : ProjectiveState) : ℝ :=
  2 / entranceStableRadius y - 2 / entranceSingleRadius y







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalSingleReciprocalError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalEntranceInput h Y 0 -
    singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

def terminalConnectionLogWalls (h : ℝ) (Y : ExitTailState) : Fin 2 → ℝ :=
  entranceLogWalls 1 (terminalConnectionState h Y)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def terminalBoundedPhaseError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalConnectionPhase h Y -
    singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def terminalBoundedPhase (h : ℝ) (Y : ExitTailState) : ℝ := 2 / terminalConnectionPhase h Y









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalNaturalPhase (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  terminalConnectionPhase (η * ((Y 0 - 2) / 2) ^ J) Y



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalNaturalState (η : ℝ) (J : ℕ) (Y : ExitTailState) : ProjectiveState :=
  terminalConnectionState (η * ((Y 0 - 2) / 2) ^ J) Y



end BianchiIX

end
end


